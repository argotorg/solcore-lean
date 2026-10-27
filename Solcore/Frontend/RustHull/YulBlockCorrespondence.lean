import Solcore.Frontend.RustHull.YulLowering
import Solcore.Frontend.RustHull.LoweringSafety
import Solcore.Frontend.RustHull.LiteralCorrespondence
import Solcore.Frontend.RustHull.YulSemantics
import Solcore.Frontend.RustHull.YulCorrespondence
import Solcore.Core.LocalLoopCorrespondence

/-! The connected inline Yul fragment through the actual `YulLowering`
builders. The proof follows the source derivation: `let` allocates the fresh
cell the lowering allocates, an assignment writes the variable's cell, a
variable reads it, and a call binds its argument words from right to left
before the builtin code runs. A nested block, `if` or `switch` is joined to the
rest of its list by `LocalLoop.sequence`; its bodies are lowered in the
enclosing context, so their locals end with them, and any control other than
fallthrough stops the list. The code of an effect builtin is a separate
obligation, `BuiltinStep`, which the frame model meets; the word primitives
compile to pure Core code, which `primitive_step` proves for every model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulBlockCorrespondence
open Core Correspondence StatementCorrespondence

/-- The continuation `lowerStatements` gives a block. -/
abbrev finish (resultType : Core.Ty) : YulLowering.Context → LowerM Core.Expr :=
  fun _ => pure (LocalLoop.fallthrough resultType)

theorem distinct_single (name : YulName) : YulLowering.distinctNames [name] = true := by
  simp only [YulLowering.distinctNames, List.map_cons, List.map_nil, decide_eq_true_eq]
  rfl

theorem words_checked {lowered : List Lowered} {done : PUnit}
    (checked : (forIn lowered PUnit.unit fun argument _ => do
        expectType Core.Ty.word argument.type
        pure (ForInStep.yield PUnit.unit) : LowerM PUnit) = .ok done) :
    ∀ argument ∈ lowered, argument.type = .word := by
  induction lowered with
  | nil => intro argument member; cases member
  | cons head rest restChecked =>
      simp only [List.forIn_cons] at checked
      obtain ⟨step, stepped, checked⟩ := lower_bind_eq_ok.mp checked
      obtain ⟨_, typed, stepped⟩ := lower_bind_eq_ok.mp stepped
      cases stepped
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact (expectType_eq_of_ok typed).symm
      · exact restChecked checked argument member

/-- The accepted lowering of a builtin call: the argument lowerings, the actual
builtin code over word temporaries, and the right-to-left argument binds. -/
theorem expr_call {fuel : Nat} {context : YulLowering.Context} {name : YulName} {arguments : List YulExpr}
    {span : Option Span} {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.call name arguments, span⟩ = .ok lowered)
    (noFunctions : context.functions = []) (notUser : name.name.startsWith "usr$" = false)
    (builtin : Effects.supports name.name = true) :
    ∃ loweredArguments effect, arguments.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments ∧
      (∀ argument ∈ loweredArguments, argument.type = .word) ∧
      Effects.lowerBuiltin (loweredArguments.foldl (fun scope _ => scope.temporary .word) context.scope)
        name.name ((List.range loweredArguments.length).map Core.Expr.var) = .ok effect ∧
      lowered = ⟨effect.type, YulLowering.bindArguments effect.type effect.expression 0 loweredArguments.reverse⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte, noFunctions, List.find?_nil,
      notUser, builtin] at compiled
    obtain ⟨loweredArguments, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, checked, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · cases compiled
    obtain ⟨effect, effectCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨loweredArguments, effect, argumentsCompiled, words_checked checked, effectCompiled, rfl⟩

/-- The accepted lowering of a call of a word primitive: the argument
lowerings, the actual `RustYulPrimitives` code over word temporaries, and the
right-to-left argument binds. -/
theorem expr_primitive {fuel : Nat} {context : YulLowering.Context} {name : YulName} {arguments : List YulExpr}
    {span : Option Span} {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.call name arguments, span⟩ = .ok lowered)
    (noFunctions : context.functions = []) (notUser : name.name.startsWith "usr$" = false)
    (notEffect : Effects.supports name.name = false) :
    ∃ loweredArguments primitive, arguments.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments ∧
      (∀ argument ∈ loweredArguments, argument.type = .word) ∧
      RustYulPrimitives.compile name.name ((List.range loweredArguments.length).map Core.Expr.var) =
        .ok primitive ∧
      lowered = ⟨primitive.type, YulLowering.bindArguments primitive.type
        (LanguageResult.success primitive.expression) 0 loweredArguments.reverse⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte, noFunctions, List.find?_nil,
      notUser, notEffect] at compiled
    obtain ⟨loweredArguments, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, checked, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · cases compiled
    split at compiled
    · rename_i value primitiveCompiled
      obtain ⟨primitive, chosen, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases chosen
      cases compiled
      exact ⟨loweredArguments, value, argumentsCompiled, words_checked checked, primitiveCompiled, rfl⟩
    · obtain ⟨_, failed, _⟩ := lower_bind_eq_ok.mp compiled
      cases failed

theorem expr_literal {fuel : Nat} {context : YulLowering.Context} {literal : YulLit} {span : Option Span}
    {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.literal literal, span⟩ = .ok lowered) :
    ∃ word, YulLowering.literalWord literal = .ok word ∧ lowered = ⟨.word, LanguageResult.success (.word word)⟩ := by
  simp only [YulLowering.lowerExpr] at compiled
  obtain ⟨word, parsed, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases compiled
  exact ⟨word, parsed, rfl⟩

theorem expr_ident {fuel : Nat} {context : YulLowering.Context} {name : YulName} {span : Option Span}
    {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.ident name, span⟩ = .ok lowered) :
    ∃ binding index, context.scope.lookup name.name = .ok (binding, index) ∧ binding.type = .word ∧
      lowered = ⟨binding.type, if binding.reference then OptionalCell.read binding.type (.var index) (Word.ofNatModulo 1)
        else LanguageResult.success (.var index)⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨value, read, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    unfold Scope.read at read
    obtain ⟨⟨binding, index⟩, looked, read⟩ := lower_bind_eq_ok.mp read
    cases read
    exact ⟨binding, index, looked, (expectType_eq_of_ok typed).symm, rfl⟩

theorem sequence_nil {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop [] (finish resultType) = .ok code) :
    code = LocalLoop.fallthrough resultType := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      exact (Except.ok.inj compiled).symm

theorem sequence_letValue {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.letDecl [name] (some value), span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered continuation, fuel = previous + 1 ∧
      name.name.startsWith Effects.reservedPrefix = false ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .word ∧
      YulLowering.lowerSequence previous ((context.temporary .word).addLocal name.name) resultType inLoop rest
        (finish resultType) = .ok continuation ∧
      code = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (.letE (OptionalCell.allocateInitialized .word (.var 0)) continuation) := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved, pure_bind] at compiled
    obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    have wordType : lowered.type = .word := (expectType_eq_of_ok typed).symm
    obtain ⟨continuation, continuationCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    rw [wordType] at continuationCompiled
    exact ⟨fuel, lowered, continuation, rfl, by simpa using reserved, valueCompiled, wordType, continuationCompiled, rfl⟩

theorem sequence_letZero {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.letDecl [name] none, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous continuation, fuel = previous + 1 ∧
      name.name.startsWith Effects.reservedPrefix = false ∧
      YulLowering.lowerSequence previous (context.addLocal name.name) resultType inLoop rest
        (finish resultType) = .ok continuation ∧
      code = .letE (OptionalCell.allocateInitialized .word (.word Word.zero)) continuation := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved, pure_bind] at compiled
    obtain ⟨continuation, continuationCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, continuation, rfl, by simpa using reserved, continuationCompiled, rfl⟩

theorem sequence_expression {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.expression value, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered next, fuel = previous + 1 ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .unit ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      code = LocalSequence.discard (LocalLoop.controlType resultType) lowered.expression next := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      exact ⟨fuel, lowered, next, rfl, valueCompiled, (expectType_eq_of_ok typed).symm, nextCompiled, rfl⟩

theorem sequence_assign {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.assign [name] value, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered next binding index, fuel = previous + 1 ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .word ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      context.scope.lookup name.name = .ok (binding, index) ∧ binding.reference = true ∧ binding.type = .word ∧
      code = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (.letE (.storeCell (.var (index + 1)) (.inRight .unit (.var 0))) ((next.weakenAt 0).weakenAt 0)) := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      simp only [YulLowering.assignMany, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at compiled
      obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨writes, written, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      have zipped : [name].zipIdx = [(name, 0)] := rfl
      simp only [zipped, List.mapM_cons, List.mapM_nil] at written
      obtain ⟨write, writeCompiled, written⟩ := lower_bind_eq_ok.mp written
      obtain ⟨others, othersDone, written⟩ := lower_bind_eq_ok.mp written
      cases othersDone
      cases written
      by_cases reserved : name.name.startsWith Effects.reservedPrefix
      · simp only [reserved, ↓reduceIte] at writeCompiled
        simp [fail, Bind.bind, Except.bind] at writeCompiled
      · simp only [reserved, Bool.false_eq_true, ↓reduceIte] at writeCompiled
        obtain ⟨⟨binding, index⟩, looked, writeCompiled⟩ := lower_bind_eq_ok.mp writeCompiled
        by_cases reference : binding.reference = true
        · simp only [reference, ↓reduceIte] at writeCompiled
          obtain ⟨_, bindingTyped, writeCompiled⟩ := lower_bind_eq_ok.mp writeCompiled
          cases writeCompiled
          exact ⟨fuel, lowered, next, binding, index, rfl, valueCompiled, (expectType_eq_of_ok typed).symm,
            nextCompiled, looked, reference, (expectType_eq_of_ok bindingTyped).symm, rfl⟩
        · simp only [reference, Bool.false_eq_true, ↓reduceIte] at writeCompiled
          simp [fail, Bind.bind, Except.bind] at writeCompiled

theorem declarations_empty {supported : String → Prop} {statements : List YulStmt}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement) :
    YulLowering.declarations statements = .ok [] := by
  unfold YulLowering.declarations
  rw [List.filterMap_eq_nil_iff.mpr ?_]
  · rfl
  · intro statement member
    cases eligible statement member <;> rfl

/-- A body of the fragment declares no local functions, so its lowering is its
statement sequence in the same context. -/
theorem block_sequence {supported : String → Prop} {fuel : Nat} {context : YulLowering.Context}
    {resultType : Core.Ty} {inLoop : Bool} {statements : List YulStmt} {code : Core.Expr}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement)
    (compiled : YulLowering.lowerBlock fuel context resultType inLoop statements (finish resultType) = .ok code) :
    ∃ previous, YulLowering.lowerSequence previous context resultType inLoop statements (finish resultType) =
      .ok code := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerBlock] at compiled
      obtain ⟨functions, declared, compiled⟩ := lower_bind_eq_ok.mp compiled
      rw [declarations_empty eligible] at declared
      cases declared
      obtain ⟨closures, closed, compiled⟩ := lower_bind_eq_ok.mp compiled
      simp only [List.mapM_nil] at closed
      cases closed
      obtain ⟨body, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      exact ⟨fuel, bodyCompiled⟩

theorem statements_sequence {supported : String → Prop} {fuel : Nat} {scope : Scope} {resultType : Core.Ty}
    {statements : List YulStmt} {signatures : List Signature} {code : Core.Expr}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement)
    (compiled : YulLowering.lowerStatements fuel scope resultType statements signatures = .ok code) :
    ∃ previous, YulLowering.lowerSequence previous {scope, hullFunctions := signatures} resultType false statements
      (finish resultType) = .ok code := by
  unfold YulLowering.lowerStatements at compiled
  obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  exact block_sequence eligible compiled

/-- The case keys and lowered bodies of a `switch`. -/
inductive Arms (fuel : Nat) (context : YulLowering.Context) (resultType : Core.Ty) (inLoop : Bool) :
    List YulCase → List (Word × Core.Expr) → Prop where
  | nil : Arms fuel context resultType inLoop [] []
  | cons {arm : YulCase} {key : Word} {code : Core.Expr} {cases : List YulCase}
      {branches : List (Word × Core.Expr)} (keyed : YulLowering.literalWord arm.lit = .ok key)
      (lowered : YulLowering.lowerBlock fuel context resultType inLoop arm.body (finish resultType) = .ok code)
      (tail : Arms fuel context resultType inLoop cases branches) :
      Arms fuel context resultType inLoop (arm :: cases) ((key, code) :: branches)

theorem arms_of_mapM {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {lower : YulCase → LowerM (Word × Core.Expr)}
    (characterized : ∀ {arm : YulCase} {key : Word} {code : Core.Expr}, lower arm = .ok (key, code) →
      YulLowering.literalWord arm.lit = .ok key ∧
        YulLowering.lowerBlock fuel context resultType inLoop arm.body (finish resultType) = .ok code) :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)}, cases.mapM lower = .ok branches →
      Arms fuel context resultType inLoop cases branches
  | [], branches, mapped => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      exact .nil
  | arm :: cases, branches, mapped => by
      simp only [List.mapM_cons] at mapped
      obtain ⟨⟨key, code⟩, first, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨others, rest, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      obtain ⟨keyed, lowered⟩ := characterized first
      exact .cons keyed lowered (arms_of_mapM characterized rest)

/-- The lowered code of a statement with nested bodies, before
`LocalLoop.sequence` joins it to the rest of the list. -/
def CompoundLowering (fuel : Nat) (context : YulLowering.Context) (resultType : Core.Ty) (inLoop : Bool) :
    YulStmt → Core.Expr → Prop
  | ⟨.block body, _⟩, head => YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok head
  | ⟨.ifThen condition body, _⟩, head => ∃ lowered tested branch,
      YulLowering.lowerExpr fuel context condition = .ok lowered ∧ YulLowering.condition lowered = .ok tested ∧
      YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok branch ∧
      head = LocalLoop.conditional resultType tested branch (LocalLoop.fallthrough resultType)
  | ⟨.switch value cases defaultBody, _⟩, head => ∃ lowered branches defaultCode,
      YulLowering.lowerExpr fuel context value = .ok lowered ∧ lowered.type = .word ∧
      Arms fuel context resultType inLoop cases branches ∧
      YulLowering.lowerBlock fuel context resultType inLoop (defaultBody.getD []) (finish resultType) =
        .ok defaultCode ∧
      head = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (YulLowering.switchBranches branches defaultCode)
  | _, _ => False

def IsCompound : YulStmt → Prop
  | ⟨.block _, _⟩ | ⟨.ifThen _ _, _⟩ | ⟨.switch _ _ _, _⟩ => True
  | _ => False

theorem sequence_compound {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {statement : YulStmt} {rest : List YulStmt} {code : Core.Expr} (compound : IsCompound statement)
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop (statement :: rest) (finish resultType) =
      .ok code) :
    ∃ previous head next, fuel = previous + 1 ∧ CompoundLowering previous context resultType inLoop statement head ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      code = LocalLoop.sequence resultType head next := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  obtain ⟨kind, span⟩ := statement
  cases kind
  all_goals try exact False.elim compound
  case block body =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨head, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, head, next, rfl, headCompiled, nextCompiled, rfl⟩
  case ifThen condition body =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨lowered, loweredCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨tested, testedCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨branch, branchCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, _, next, rfl, ⟨lowered, tested, branch, loweredCompiled, testedCompiled, branchCompiled, rfl⟩,
      nextCompiled, rfl⟩
  case switch value cases defaultBody =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨lowered, loweredCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨branches, branchesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · obtain ⟨defaultCode, defaultCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      refine ⟨fuel, _, next, rfl, ⟨lowered, branches, defaultCode, loweredCompiled, (expectType_eq_of_ok typed).symm,
        arms_of_mapM ?_ branchesCompiled, defaultCompiled, rfl⟩, nextCompiled, rfl⟩
      intro arm key code mapped
      obtain ⟨_, keyed, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨_, lowered, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      exact ⟨keyed, lowered⟩
    · simp [fail, Bind.bind, Except.bind] at compiled

theorem condition_components {lowered : Lowered} {tested : Core.Expr}
    (compiled : YulLowering.condition lowered = .ok tested) :
    lowered.type = .word ∧ tested = LanguageResult.bind .bool lowered.expression
      (LanguageResult.success (.unary .boolNot (.binary .wordEq (.var 0) (.word Word.zero)))) := by
  unfold YulLowering.condition at compiled
  obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases compiled
  exact ⟨(expectType_eq_of_ok typed).symm, rfl⟩

/-- The argument lowerings of a call, each a word. -/
inductive Lowers (fuel : Nat) (context : YulLowering.Context) : List YulExpr → List Lowered → Prop where
  | nil : Lowers fuel context [] []
  | cons {expression : YulExpr} {lowered : Lowered} {expressions : List YulExpr} {loweredArguments : List Lowered}
      (head : YulLowering.lowerExpr fuel context expression = .ok lowered) (typed : lowered.type = .word)
      (tail : Lowers fuel context expressions loweredArguments) :
      Lowers fuel context (expression :: expressions) (lowered :: loweredArguments)

theorem Lowers.concat {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered}, Lowers fuel context expressions loweredArguments →
      ∀ {expression : YulExpr} {lowered : Lowered}, YulLowering.lowerExpr fuel context expression = .ok lowered →
        lowered.type = .word → Lowers fuel context (expressions ++ [expression]) (loweredArguments ++ [lowered])
  | _, _, .nil, _, _, head, typed => .cons head typed .nil
  | _, _, .cons first firstTyped tail, _, _, head, typed => .cons first firstTyped (tail.concat head typed)

theorem Lowers.reverse {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered}, Lowers fuel context expressions loweredArguments →
      Lowers fuel context expressions.reverse loweredArguments.reverse
  | _, _, .nil => .nil
  | _, _, .cons head typed tail => by
      simp only [List.reverse_cons]
      exact tail.reverse.concat head typed

theorem lowers_of_mapM {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered},
      expressions.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments →
      (∀ lowered ∈ loweredArguments, lowered.type = .word) → Lowers fuel context expressions loweredArguments
  | [], loweredArguments, mapped, _ => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      exact .nil
  | expression :: expressions, loweredArguments, mapped, typed => by
      simp only [List.mapM_cons] at mapped
      obtain ⟨lowered, head, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨others, tail, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      exact .cons head (typed lowered (List.mem_cons.mpr (.inl rfl)))
        (lowers_of_mapM tail fun other member => typed other (List.mem_cons.mpr (.inr member)))

/-- The renaming under `count` Core binders. -/
def liftN (mapping : Renaming) : Nat → Renaming
  | 0 => mapping
  | count + 1 => (liftN mapping count).lift

theorem liftN_below (mapping : Renaming) : ∀ {count index : Nat}, index < count → liftN mapping count index = index
  | count + 1, 0, _ => rfl
  | count + 1, index + 1, below => by
      show liftN mapping count index + 1 = index + 1
      rw [liftN_below mapping (Nat.lt_of_succ_lt_succ below)]

theorem liftN_add (mapping : Renaming) : ∀ (count index : Nat), liftN mapping count (index + count) = mapping index + count
  | 0, _ => rfl
  | count + 1, index => by
      show liftN mapping count (index + count) + 1 = mapping index + (count + 1)
      rw [liftN_add mapping count index]
      rfl

/-- An argument lowered in the call's scope and bound under `count` earlier
argument words. -/
theorem shifted_rename (expression : Core.Expr) (mapping : Renaming) (count : Nat) :
    (expression.rename (· + count)).rename (liftN mapping count) =
      expression.rename (fun index => count + mapping index) := by
  rw [Expr.rename_comp]
  congr 1
  funext index
  show liftN mapping count (index + count) = count + mapping index
  rw [liftN_add, Nat.add_comm]

theorem weakened_once (expression : Core.Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = expression.rename (fun index => 1 + mapping index) := by
  rw [LocalLoop.rename_weaken_zero, LocalLoop.weaken_zero, Expr.rename_comp]
  rfl

theorem weakened_twice (expression : Core.Expr) (mapping : Renaming) :
    ((expression.weakenAt 0).weakenAt 0).rename mapping.lift.lift =
      expression.rename (fun index => 2 + mapping index) := by
  rw [LocalLoop.rename_weaken_zero, LocalLoop.rename_weaken_zero, LocalLoop.weaken_zero, LocalLoop.weaken_zero,
    LocalLoop.rename_shift, Expr.rename_comp]
  rfl

theorem renamed_weakened (expression : Core.Expr) (mapping : Renaming) :
    (expression.rename mapping).weakenAt 0 = expression.rename (fun index => 1 + mapping index) := by
  rw [LocalLoop.weaken_zero, Expr.rename_comp]
  rfl

/-- Builtin argument temporaries hide no effect slot. -/
theorem temporaries_lookup {α : Type} : ∀ (items : List α) (scope : Scope) {name : String} {binding : Binding}
    {index : Nat}, (items.foldl (fun scope _ => scope.temporary .word) scope).lookup name = .ok (binding, index) →
    ∃ previous, scope.lookup name = .ok (binding, previous) ∧ index = previous + items.length
  | [], _, _, _, index, looked => ⟨index, looked, rfl⟩
  | _ :: rest, scope, name, binding, _, looked => by
      obtain ⟨middle, middleLooked, rfl⟩ := temporaries_lookup rest (scope.temporary .word) looked
      rw [Scope.temporary, scope_lookup_cons] at middleLooked
      simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at middleLooked
      cases previous : scope.lookup name with
      | error error => simp only [previous] at middleLooked; contradiction
      | ok found =>
          rcases found with ⟨oldBinding, oldIndex⟩
          simp only [previous, Except.ok.injEq, Prod.mk.injEq] at middleLooked
          obtain ⟨rfl, rfl⟩ := middleLooked
          refine ⟨oldIndex, rfl, ?_⟩
          simp only [List.length_cons]
          omega

theorem temporaries_related {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} (related : EffectEnvironmentRel slots scope mapping environment)
    {α : Type} (items : List α) (values : Environment) (length : values.length = items.length) :
    EffectEnvironmentRel slots (items.foldl (fun scope _ => scope.temporary .word) scope)
      (liftN mapping items.length) (values ++ environment) := by
  intro slot member binding index looked
  obtain ⟨previous, previousLooked, rfl⟩ := temporaries_lookup items scope looked
  rw [liftN_add, ← length, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
  exact related slot member binding previous previousLooked

theorem word_result {source : Word} {target : Value} (related : ResultRel .word (.value (.word source)) target) :
    target = .inRight .word (.word source) := by
  cases related with
  | value related =>
      cases related
      rfl

theorem unit_result {target : Value} (related : ResultRel .unit (.value .unit) target) :
    target = .inRight .word .unit := by
  cases related with
  | value related =>
      cases related
      rfl

theorem literal_word {literal : YulLit} {lowered source : Word}
    (compiled : YulLowering.literalWord literal = .ok lowered)
    (evaluated : YulSemantics.literalWord? literal = some source) : lowered = source := by
  cases literal with
  | number text | hex text =>
      have parsed := Correspondence.parseWord_some_of_ok compiled
      exact Option.some.inj (parsed.symm.trans evaluated)
  | bool value =>
      exact (Except.ok.inj compiled).symm.trans (Option.some.inj evaluated)
  | string text => cases evaluated

theorem literal_word_some {literal : YulLit} {word : Word} (compiled : YulLowering.literalWord literal = .ok word)
    (notString : ∀ text, literal ≠ .string text) : YulSemantics.literalWord? literal = some word := by
  cases literal with
  | number text | hex text => exact Correspondence.parseWord_some_of_ok compiled
  | bool value => exact congrArg some (Except.ok.inj compiled)
  | string text => exact (notString text rfl).elim

theorem select_mem {word : Word} : ∀ {cases : List YulCase} {body : List YulStmt},
    YulSemantics.select word cases = some body → ∃ arm ∈ cases, arm.body = body
  | [], _, selected => by cases selected
  | arm :: rest, body, selected => by
      simp only [YulSemantics.select] at selected
      split at selected
      · cases selected
        exact ⟨arm, List.mem_cons.mpr (.inl rfl), rfl⟩
      · obtain ⟨other, member, same⟩ := select_mem selected
        exact ⟨other, List.mem_cons.mpr (.inr member), same⟩

/-- The chain of case tests reaches the body of the first case whose key is the
scrutinee word. -/
theorem switch_selected {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {mapping : Renaming} {environment : Environment} {word : Word} :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)} {body : List YulStmt},
      Arms fuel context resultType inLoop cases branches → (∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text) →
      YulSemantics.select word cases = some body →
      ∃ code, YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok code ∧
        ∀ {defaultCode : Core.Expr} {store finalStore : Store} {result : Value},
          Evaluates (.word word :: environment) store (code.rename (fun index => 1 + mapping index)) result
            finalStore →
          Evaluates (.word word :: environment) store
            ((YulLowering.switchBranches branches defaultCode).rename mapping.lift) result finalStore
  | _, _, _, .nil, _, selected => by cases selected
  | arm :: _, (key, code) :: _, _, .cons keyed lowered tail, literals, selected => by
      have source := literal_word_some keyed (literals arm (List.mem_cons.mpr (.inl rfl)))
      simp only [YulSemantics.select] at selected
      by_cases same : YulSemantics.literalWord? arm.lit = some word
      · rw [if_pos same] at selected
        cases selected
        have equal : key = word := Option.some.inj (source.symm.trans same)
        subst equal
        refine ⟨code, lowered, fun evaluated => ?_⟩
        apply Evaluates.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply]))
        rw [weakened_once]
        exact evaluated
      · rw [if_neg same] at selected
        obtain ⟨found, foundLowered, chain⟩ :=
          switch_selected tail (fun other member => literals other (List.mem_cons.mpr (.inr member))) selected
        refine ⟨found, foundLowered, fun evaluated => ?_⟩
        have different : word ≠ key := fun equal => same (equal ▸ source)
        apply Evaluates.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, different]))
        exact chain evaluated

/-- Without a matching case the chain of case tests reaches the default body. -/
theorem switch_unselected {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {mapping : Renaming} {environment : Environment} {word : Word} :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)},
      Arms fuel context resultType inLoop cases branches → (∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text) →
      YulSemantics.select word cases = none →
      ∀ {defaultCode : Core.Expr} {store finalStore : Store} {result : Value},
        Evaluates (.word word :: environment) store (defaultCode.rename (fun index => 1 + mapping index)) result
          finalStore →
        Evaluates (.word word :: environment) store
          ((YulLowering.switchBranches branches defaultCode).rename mapping.lift) result finalStore
  | _, _, .nil, _, _, defaultCode, _, _, _, evaluated => by
      show Evaluates _ _ ((defaultCode.weakenAt 0).rename mapping.lift) _ _
      rw [weakened_once]
      exact evaluated
  | arm :: _, (key, _) :: _, .cons keyed _ tail, literals, unselected, _, _, _, _, evaluated => by
      have source := literal_word_some keyed (literals arm (List.mem_cons.mpr (.inl rfl)))
      simp only [YulSemantics.select] at unselected
      by_cases same : YulSemantics.literalWord? arm.lit = some word
      · rw [if_pos same] at unselected
        cases unselected
      · rw [if_neg same] at unselected
        have different : word ≠ key := fun equal => same (equal ▸ source)
        apply Evaluates.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, different]))
        exact switch_unselected tail (fun other member => literals other (List.mem_cons.mpr (.inr member)))
          unselected evaluated

theorem condition_evaluates {environment : Environment} {store finalStore : Store} {mapping : Renaming}
    {expression : Core.Expr} {word : Word}
    (evaluated : Evaluates environment store (expression.rename mapping) (.inRight .word (.word word)) finalStore) :
    Evaluates environment store ((LanguageResult.bind .bool expression
        (LanguageResult.success (.unary .boolNot (.binary .wordEq (.var 0) (.word Word.zero))))).rename mapping)
      (.inRight .word (.bool (!(word == Word.zero)))) finalStore :=
  LanguageResult.bind_success .bool evaluated
    (LanguageResult.success_evaluates (.unary (.binary (.var rfl) .word rfl) rfl))

/-- A nested statement that falls through continues with the rest of the list
under the three binders of `LocalLoop.sequence`. -/
theorem sequence_next {type : Core.Ty} {first next : Core.Expr} {mapping : Renaming} {environment : Environment}
    {initial middle final : Store} {result : Value}
    (firstEvaluated : Evaluates environment initial (first.rename mapping) (LocalLoop.fallthroughValue type) middle)
    (nextEvaluated : Evaluates
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (next.rename (fun index => 3 + mapping index)) result final) :
    Evaluates environment initial ((LocalLoop.sequence type first next).rename mapping) result final :=
  StatementCorrespondence.sequence_fallthrough firstEvaluated (by simpa only [Nat.add_comm] using nextEvaluated)

/-- Any other control of a nested statement stops the list. -/
theorem sequence_stopped {type : Core.Ty} {first next : Core.Expr} {mapping : Renaming} {environment : Environment}
    {initial final : Store} {control : Semantics.Control} {target : Value}
    (related : ControlRel type control target) (stopped : control ≠ .fallthrough)
    (evaluated : Evaluates environment initial (first.rename mapping) target final) :
    Evaluates environment initial ((LocalLoop.sequence type first next).rename mapping) target final := by
  rw [rename_sequence]
  cases related with
  | fallthrough => exact (stopped rfl).elim
  | returned _ => exact LocalLoop.sequence_returned _ evaluated
  | breaking => exact LocalLoop.sequence_transfer _ evaluated
  | continuing => exact LocalLoop.sequence_transfer _ evaluated
  | language reason => exact LocalLoop.sequence_failure _ evaluated

theorem Compound.isCompound {environment : Semantics.Environment} {statement : YulStmt}
    {initial final : YulSemantics.State} {control : Semantics.Control}
    (compound : YulSemantics.Compound environment statement initial control final) : IsCompound statement := by
  cases compound <;> trivial

/-- A builtin of the fragment is lowered either by `Effects.lowerBuiltin` or as a
pure `RustYulPrimitives` operation. -/
theorem builtin_named {name : String} (named : name ∈ YulSemantics.builtins) :
    name.startsWith Effects.reservedPrefix = false ∧ name.startsWith "usr$" = false ∧
      ((name ∈ YulSemantics.effectBuiltins ∧ Effects.supports name = true) ∨
        (name ∈ YulFragment.primitives ∧ Effects.supports name = false)) := by
  simp only [YulSemantics.builtins, YulSemantics.effectBuiltins, YulFragment.primitives, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at named
  rcases named with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide +kernel

theorem Builtin.named {name : String} {words : List Word} {frame next : RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value} (computed : YulSemantics.Builtin name words frame result next) :
    name ∈ YulSemantics.builtins := by
  cases computed <;> decide

/-- The Core code of a two-argument word primitive, over the innermost values in
source order. -/
def binaryCode (body : Core.Expr) : Core.Expr :=
  .apply (.lambda .word .word (.apply (.lambda .word .word body) (.var 1))) (.var 1)

/-- The Core code of a one-argument word primitive. -/
def unaryCode (body : Core.Expr) : Core.Expr :=
  .apply (.lambda .word .word body) (.var 0)

theorem binaryCode_evaluates {body : Core.Expr} {mapping : Renaming} {environment : Environment}
    {store : Store} {left right : Word} {result : Value} (first : mapping 0 = 0) (second : mapping 1 = 1)
    (evaluated : Evaluates (.word left :: .word right :: .word left :: .word right :: environment) store
      (body.rename mapping.lift.lift) result store) :
    Evaluates (.word left :: .word right :: environment) store ((binaryCode body).rename mapping) result store := by
  apply Evaluates.apply .lambda (.var (by show (_ :: _ :: environment)[mapping 1]? = _; rw [second]; rfl))
  apply Evaluates.apply .lambda
    (.var (by show (_ :: _ :: _ :: environment)[mapping 0 + 1]? = _; rw [first]; rfl))
  exact evaluated

theorem unaryCode_evaluates {body : Core.Expr} {mapping : Renaming} {environment : Environment}
    {store : Store} {value : Word} {result : Value} (first : mapping 0 = 0)
    (evaluated : Evaluates (.word value :: .word value :: environment) store (body.rename mapping.lift) result store) :
    Evaluates (.word value :: environment) store ((unaryCode body).rename mapping) result store := by
  apply Evaluates.apply .lambda (.var (by show (_ :: environment)[mapping 0]? = _; rw [first]; rfl))
  exact evaluated

/-- The word primitives run their actual `RustYulPrimitives` code over the
argument words and leave the frame unchanged, in every effect model. -/
theorem primitive_step {name : String} {words : List Word} {frame next : RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value} (computed : YulSemantics.Builtin name words frame result next)
    (primitive : name ∈ YulFragment.primitives) {lowered : RustYulPrimitives.Lowered}
    (compiled : RustYulPrimitives.compile name ((List.range words.length).map Core.Expr.var) = .ok lowered)
    {mapping : Renaming} {environment : Environment} {store : Store}
    (fixed : ∀ index < words.length, mapping index = index) :
    next = frame ∧ ∃ target, ResultRel lowered.type result target ∧
      Evaluates (words.map Value.word ++ environment) store
        ((LanguageResult.success lowered.expression).rename mapping) target store := by
  cases computed with
  | mload => exact absurd primitive (by decide)
  | msize => exact absurd primitive (by decide)
  | mstore => exact absurd primitive (by decide)
  | mstore8 => exact absurd primitive (by decide)
  | returned => exact absurd primitive (by decide)
  | reverted => exact absurd primitive (by decide)
  | @add _ left right =>
      have code : RustYulPrimitives.compile "add" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.binary .wordAdd (.var 0) (.var 1))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      exact ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) (.binary (.var rfl) (.var rfl) rfl))⟩
  | @sub _ left right =>
      have code : RustYulPrimitives.compile "sub" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.binary .wordSub (.var 0) (.var 1))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      exact ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) (.binary (.var rfl) (.var rfl) rfl))⟩
  | @lt _ left right =>
      have code : RustYulPrimitives.compile "lt" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordGt (.var 1) (.var 0)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases below : left < right
      · rw [if_pos below]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, below])) .word
      · rw [if_neg below]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, below])) .word
  | @gt _ left right =>
      have code : RustYulPrimitives.compile "gt" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordGt (.var 0) (.var 1)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases above : left > right
      · rw [if_pos above]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, above])) .word
      · rw [if_neg above]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, above])) .word
  | @eq _ left right =>
      have code : RustYulPrimitives.compile "eq" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordEq (.var 0) (.var 1)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases same : left = right
      · rw [if_pos same]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, same])) .word
      · rw [if_neg same]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, same])) .word
  | @iszero _ value =>
      have code : RustYulPrimitives.compile "iszero" [.var 0] =
          .ok ⟨.word, unaryCode (.ifE (.binary .wordEq (.var 0) (.word Word.zero)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [value].length).map Core.Expr.var = [.var 0] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates (unaryCode_evaluates (fixed 0 (by simp)) ?_)⟩
      by_cases zero : value = Word.zero
      · rw [if_pos zero]
        exact .ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply, zero])) .word
      · rw [if_neg zero]
        exact .ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, zero])) .word

/-- The builtin obligation of an effect model: the actual code of an effect
builtin over its argument words, bound as the innermost Core values, simulates
`YulSemantics.Builtin`. -/
def BuiltinStep (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot) : Prop :=
  ∀ {name : String} {words : List Word} {state : YulSemantics.State} {result : Semantics.Result Semantics.Value}
    {next : RuntimeEffectsSemantics.State} {scope : Scope} {effect : Lowered} {mapping : Renaming}
    {environment : Environment} {world : World} {store : Store},
    name ∈ YulSemantics.effectBuiltins →
    YulSemantics.Builtin name words (YulSemantics.frame state) result next →
    Effects.lowerBuiltin scope name ((List.range words.length).map Core.Expr.var) = .ok effect →
    EffectEnvironmentRel slots scope mapping (words.map Value.word ++ environment) →
    (∀ index < words.length, mapping index = index) →
    StateRel model world state store →
    ∃ target finalStore, ResultRel effect.type result target ∧
      Evaluates (words.map Value.word ++ environment) store (effect.expression.rename mapping) target finalStore ∧
      StateRel model world (YulSemantics.withFrame state next) finalStore ∧ ClosuresPreserved store finalStore

section Simulation
variable {model : StateModel RuntimeCallEffectsSemantics.State} {slots : List EffectSlot}

/-- An accepted expression lowering simulates the source evaluation. -/
def ExpressionGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (sourceEnvironment : Semantics.Environment) (expression : YulExpr) (initial : YulSemantics.State)
    (result : Semantics.Result Semantics.Value) (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {lowered : Lowered}, context.functions = [] →
    YulLowering.lowerExpr fuel context expression = .ok lowered →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ target finalStore, ResultRel lowered.type result target ∧
        Evaluates environment store (lowered.expression.rename mapping) target finalStore ∧
        StateRel model world final finalStore ∧ ClosuresPreserved store finalStore

/-- Argument binds under the words `bound` before them: their words reach the
body, or their first fault stops it. -/
def ArgumentsGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (sourceEnvironment : Semantics.Environment) (expressions : List YulExpr) (initial : YulSemantics.State) :
    Semantics.Result (List Word) → YulSemantics.State → Prop
  | .value words, final =>
      ∀ {fuel : Nat} {context : YulLowering.Context} {loweredArguments : List Lowered}, context.functions = [] →
        Lowers fuel context expressions loweredArguments →
        ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
          EnvironmentRel world sourceEnvironment context.scope mapping environment →
          EffectEnvironmentRel slots context.scope mapping environment →
          StateRel model world initial store → ∀ (bound : Environment) (type : Core.Ty) (body : Core.Expr),
          ∃ middleStore, words.length = loweredArguments.length ∧ StateRel model world final middleStore ∧
            ClosuresPreserved store middleStore ∧
            ∀ {result : Value} {finalStore : Store},
              Evaluates ((words.map Value.word).reverse ++ bound ++ environment) middleStore
                (body.rename (liftN mapping (bound.length + words.length))) result finalStore →
              Evaluates (bound ++ environment) store
                ((YulLowering.bindArguments type body bound.length loweredArguments).rename (liftN mapping bound.length))
                result finalStore
  | .fault reason, final =>
      ∀ {fuel : Nat} {context : YulLowering.Context} {loweredArguments : List Lowered}, context.functions = [] →
        Lowers fuel context expressions loweredArguments →
        ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
          EnvironmentRel world sourceEnvironment context.scope mapping environment →
          EffectEnvironmentRel slots context.scope mapping environment →
          StateRel model world initial store → ∀ (bound : Environment) (type : Core.Ty) (body : Core.Expr),
          ∃ reasonWord finalStore, reason = .language reasonWord ∧ StateRel model world final finalStore ∧
            ClosuresPreserved store finalStore ∧
            Evaluates (bound ++ environment) store
              ((YulLowering.bindArguments type body bound.length loweredArguments).rename (liftN mapping bound.length))
              (.inLeft type (.word reasonWord)) finalStore

theorem expression_simulation (step : BuiltinStep model slots) {sourceEnvironment : Semantics.Environment}
    {expression : YulExpr} {initial final : YulSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : YulSemantics.Eval sourceEnvironment expression initial result final) :
    ExpressionGoal model slots sourceEnvironment expression initial result final := by
  refine YulSemantics.Eval.rec
    (motive_1 := fun expression initial result final _ =>
      ExpressionGoal model slots sourceEnvironment expression initial result final)
    (motive_2 := fun expressions initial result final _ =>
      ArgumentsGoal model slots sourceEnvironment expressions initial result final)
    ?literal ?ident ?call ?callFault ?nil ?cons ?tailFault ?headFault evaluated
  case literal =>
    intro literal span state word evaluated fuel context lowered _ compiled world mapping environment store _ _
      stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨loweredWord, parsed, rfl⟩ := expr_literal compiled
        cases literal_word parsed evaluated
        exact ⟨_, store, .value (.word _), LanguageResult.success_evaluates .word, stateRelated,
          ClosuresPreserved.refl store⟩
  case ident =>
    intro name span state location word found read fuel context lowered _ compiled world mapping environment store
      environmentRelated _ stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨binding, index, looked, wordType, rfl⟩ := expr_ident compiled
        obtain ⟨cellLocation, targetValue, reference, targetFound, cellRead, valueRelated⟩ :=
          environmentRelated.read stateRelated.toHeapRel found looked read
        rw [wordType] at targetFound valueRelated
        cases valueRelated
        simp only [reference, ↓reduceIte]
        rw [wordType]
        exact ⟨_, store, .value (.word word), OptionalCell.read_success _ (.var targetFound) cellRead, stateRelated,
          ClosuresPreserved.refl store⟩
  case call =>
    intro name arguments span initial middle words result next _ computed argumentsSimulated
      fuel context lowered noFunctions compiled world mapping environment store environmentRelated runtime stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨_, notUser, kind⟩ := builtin_named (Builtin.named computed)
        rcases kind with ⟨effectNamed, builtin⟩ | ⟨primitiveNamed, notEffect⟩
        · obtain ⟨loweredArguments, effect, argumentsCompiled, typed, effectCompiled, rfl⟩ :=
            expr_call compiled noFunctions notUser builtin
          obtain ⟨middleStore, lengthEq, middleState, firstFrame, continued⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] effect.type effect.expression
          have count : words.reverse.length = loweredArguments.length := by simpa using lengthEq
          obtain ⟨target, finalStore, related, effectEvaluated, finalState, lastFrame⟩ :=
            step effectNamed computed (by rw [count]; exact effectCompiled)
              (temporaries_related runtime loweredArguments (words.reverse.map Value.word) (by simpa using count))
              (fun index below => liftN_below mapping (count ▸ below)) middleState
          refine ⟨target, finalStore, related, continued ?_, finalState, firstFrame.trans lastFrame⟩
          have sameLength : ([] : Environment).length + words.length = loweredArguments.length := by
            simpa using count
          rw [sameLength, List.append_nil, ← List.map_reverse]
          exact effectEvaluated
        · obtain ⟨loweredArguments, primitive, argumentsCompiled, typed, primitiveCompiled, rfl⟩ :=
            expr_primitive compiled noFunctions notUser notEffect
          obtain ⟨middleStore, lengthEq, middleState, firstFrame, continued⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] primitive.type (LanguageResult.success primitive.expression)
          have count : words.reverse.length = loweredArguments.length := by simpa using lengthEq
          obtain ⟨rfl, target, related, primitiveEvaluated⟩ :=
            primitive_step (environment := environment) (store := middleStore) computed primitiveNamed
              (by rw [count]; exact primitiveCompiled) (fun index below => liftN_below mapping (count ▸ below))
          refine ⟨target, middleStore, related, continued ?_, middleState, firstFrame⟩
          have sameLength : ([] : Environment).length + words.length = loweredArguments.length := by
            simpa using count
          rw [sameLength, List.append_nil, ← List.map_reverse]
          exact primitiveEvaluated
  case callFault =>
    intro name arguments span initial final reason named _ argumentsSimulated
      fuel context lowered noFunctions compiled world mapping environment store environmentRelated runtime stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨_, notUser, kind⟩ := builtin_named named
        rcases kind with ⟨_, builtin⟩ | ⟨_, notEffect⟩
        · obtain ⟨loweredArguments, effect, argumentsCompiled, typed, _, rfl⟩ :=
            expr_call compiled noFunctions notUser builtin
          obtain ⟨reasonWord, finalStore, rfl, finalState, frame, faulted⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] effect.type effect.expression
          exact ⟨_, finalStore, .language reasonWord, faulted, finalState, frame⟩
        · obtain ⟨loweredArguments, primitive, argumentsCompiled, typed, _, rfl⟩ :=
            expr_primitive compiled noFunctions notUser notEffect
          obtain ⟨reasonWord, finalStore, rfl, finalState, frame, faulted⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] primitive.type (LanguageResult.success primitive.expression)
          exact ⟨_, finalStore, .language reasonWord, faulted, finalState, frame⟩
  case nil =>
    intro state fuel context loweredArguments _ lowers world mapping environment store _ _ stateRelated bound type body
    cases lowers
    exact ⟨store, rfl, stateRelated, ClosuresPreserved.refl store, fun evaluated => evaluated⟩
  case cons =>
    intro argument rest initial middle final word words _ _ headSimulated tailSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, headStore, headRelated, headEvaluated, headState, headFrame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    rw [headTyped] at headRelated
    obtain rfl := word_result headRelated
    obtain ⟨middleStore, lengthEq, middleState, tailFrame, continued⟩ :=
      tailSimulated noFunctions tailLowers environmentRelated runtime headState (.word word :: bound) type body
    refine ⟨middleStore, by simp [lengthEq], middleState, headFrame.trans tailFrame, ?_⟩
    intro result finalStore evaluated
    have reshaped : Evaluates ((words.map Value.word).reverse ++ (Value.word word :: bound) ++ environment) middleStore
        (body.rename (liftN mapping ((Value.word word :: bound).length + words.length))) result finalStore := by
      have indexEq : (Value.word word :: bound).length + words.length = bound.length + (word :: words).length := by
        simp only [List.length_cons]
        omega
      rw [indexEq]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using evaluated
    exact LanguageResult.bind_success type (by rw [shifted_rename]; exact headEvaluated) (continued reshaped)
  case tailFault =>
    intro argument rest initial middle final word reason _ _ headSimulated tailSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, headStore, headRelated, headEvaluated, headState, headFrame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    rw [headTyped] at headRelated
    obtain rfl := word_result headRelated
    obtain ⟨reasonWord, finalStore, rfl, finalState, tailFrame, tailEvaluated⟩ :=
      tailSimulated noFunctions tailLowers environmentRelated runtime headState (.word word :: bound) type body
    exact ⟨reasonWord, finalStore, rfl, finalState, headFrame.trans tailFrame,
      LanguageResult.bind_success type (by rw [shifted_rename]; exact headEvaluated) tailEvaluated⟩
  case headFault =>
    intro argument rest initial final reason _ headSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, finalStore, headRelated, headEvaluated, finalState, frame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    cases headRelated with
    | language reasonWord =>
        exact ⟨reasonWord, finalStore, rfl, finalState, frame,
          LanguageResult.bind_failure type (by rw [shifted_rename]; exact headEvaluated)⟩

/-- An accepted statement list simulates the source run. -/
def RunGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (supported : String → Prop) (resultType : Core.Ty) (sourceEnvironment : Semantics.Environment)
    (body : List YulStmt) (initial : YulSemantics.State) (control : Semantics.Control)
    (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {inLoop : Bool} {code : Core.Expr}, context.functions = [] →
    (∀ statement ∈ body, YulFragment.StatementEligible supported statement) →
    YulLowering.lowerSequence fuel context resultType inLoop body (finish resultType) = .ok code →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ extension target finalStore, ControlRel resultType control target ∧
        Evaluates environment store (code.rename mapping) target finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore

/-- The code of an accepted statement with nested bodies simulates its source
run. -/
def CompoundGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (supported : String → Prop) (resultType : Core.Ty) (sourceEnvironment : Semantics.Environment)
    (statement : YulStmt) (initial : YulSemantics.State) (control : Semantics.Control)
    (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {inLoop : Bool} {head : Core.Expr}, context.functions = [] →
    YulFragment.StatementEligible supported statement →
    CompoundLowering fuel context resultType inLoop statement head →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ extension target finalStore, ControlRel resultType control target ∧
        Evaluates environment store (head.rename mapping) target finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore

theorem sequence_simulation (step : BuiltinStep model slots) {supported : String → Prop} {resultType : Core.Ty}
    {sourceEnvironment : Semantics.Environment} {body : List YulStmt} {initial final : YulSemantics.State}
    {control : Semantics.Control} (executed : YulSemantics.Run sourceEnvironment body initial control final) :
    RunGoal model slots supported resultType sourceEnvironment body initial control final := by
  refine YulSemantics.Run.rec
    (motive_1 := fun sourceEnvironment body initial control final _ =>
      RunGoal model slots supported resultType sourceEnvironment body initial control final)
    (motive_2 := fun sourceEnvironment statement initial control final _ =>
      CompoundGoal model slots supported resultType sourceEnvironment statement initial control final)
    ?nil ?letValue ?letZero ?letFault ?assign ?assignFault ?expression ?expressionFault ?compound ?compoundStop
    ?block ?ifTrue ?ifFalse ?ifFault ?switchCase ?switchDefault ?switchFault executed
  case nil =>
    intro sourceEnvironment state fuel context inLoop code _ _ compiled world mapping environment store _ _
      stateRelated
    obtain rfl := sequence_nil compiled
    exact ⟨[], _, store, .fallthrough, LocalLoop.fallthrough_evaluates _ _ _,
      by simpa only [List.append_nil] using stateRelated, ClosuresPreserved.refl store⟩
  case letValue =>
    intro sourceEnvironment name value span rest initial middle final control word evaluated _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, continuation, rfl, allowed, valueCompiled, wordType, continuationCompiled, rfl⟩ :=
      sequence_letValue compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    have entry : (world ++ [(Core.Ty.word, middleStore.length)])[middle.heap.length]? =
        some (Core.Ty.word, middleStore.length) := by
      rw [← middleState.length_eq, List.getElem?_concat_length]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated (context := (context.temporary .word).addLocal name.name)
        (by simp [YulLowering.Context.addLocal, YulLowering.Context.temporary, YulLowering.Context.push, noFunctions])
        (fun other member => eligible other (List.mem_cons.mpr (.inr member)))
        continuationCompiled
        (((environmentRelated.extendWorld [(.word, middleStore.length)]).temporary .word (.word word)).addLocal
          name.name .word middle.heap.length middleStore.length entry)
        ((runtime.temporary .word (.word word)).addLocal name.name .word
          (.cellRef (OptionalCell.cellType .word) middleStore.length) allowed)
        (middleState.allocate (.word word))
    refine ⟨[(.word, middleStore.length)] ++ extension, target, finalStore, related, ?_,
      by simpa only [List.append_assoc] using finalState,
      firstFrame.trans (ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame)⟩
    exact LanguageResult.bind_success _ valueEvaluated
      (Evaluates.letE (OptionalCell.allocateInitialized_evaluates (.var rfl)) tailEvaluated)
  case letZero =>
    intro sourceEnvironment name span rest initial final control _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, continuation, rfl, allowed, continuationCompiled, rfl⟩ := sequence_letZero compiled
    have entry : (world ++ [(Core.Ty.word, store.length)])[initial.heap.length]? =
        some (Core.Ty.word, store.length) := by
      rw [← stateRelated.length_eq, List.getElem?_concat_length]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated (context := context.addLocal name.name)
        (by simp [YulLowering.Context.addLocal, YulLowering.Context.push, noFunctions])
        (fun other member => eligible other (List.mem_cons.mpr (.inr member)))
        continuationCompiled
        ((environmentRelated.extendWorld [(.word, store.length)]).addLocal name.name .word initial.heap.length
          store.length entry)
        (runtime.addLocal name.name .word (.cellRef (OptionalCell.cellType .word) store.length) allowed)
        (stateRelated.allocate (.word Word.zero))
    refine ⟨[(.word, store.length)] ++ extension, target, finalStore, related, ?_,
      by simpa only [List.append_assoc] using finalState, ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame⟩
    exact Evaluates.letE (OptionalCell.allocateInitialized_evaluates .word) tailEvaluated
  case letFault =>
    intro sourceEnvironment name value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, continuation, rfl, _, valueCompiled, _, _, rfl⟩ := sequence_letValue compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case assign =>
    intro sourceEnvironment name value span rest initial middle final control word location evaluated found _
      tailSimulated fuel context inLoop code noFunctions eligible compiled world mapping environment store
      environmentRelated runtime stateRelated
    obtain ⟨previous, lowered, next, binding, index, rfl, valueCompiled, wordType, nextCompiled, looked, reference,
      bindingWord, rfl⟩ := sequence_assign compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨cellLocation, entry, _, targetFound⟩ := environmentRelated name.name location binding index found looked
    rw [bindingWord] at entry targetFound
    obtain ⟨_, oldValue, _, oldRead, _⟩ := middleState.cell location .word cellLocation entry
    have written : middleStore.write? cellLocation (.inRight .unit (.word word)) =
        some (middleStore.set cellLocation (.inRight .unit (.word word))) :=
      Store.write?_eq_some_iff.mpr ⟨middleState.location_bound entry, rfl⟩
    have nextEnvironment : EnvironmentRel world sourceEnvironment context.scope (fun index => 2 + mapping index)
        (.unit :: .word word :: environment) := environmentRelated.prepend [.unit, .word word]
    have nextRuntime : EffectEnvironmentRel slots context.scope (fun index => 2 + mapping index)
        (.unit :: .word word :: environment) := runtime.prepend [.unit, .word word]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        nextEnvironment nextRuntime (middleState.write entry (.word word) written)
    refine ⟨extension, target, finalStore, related, ?_, finalState,
      firstFrame.trans (ClosuresPreserved.trans (ClosuresPreserved.write middleState.toHeapRel entry written) lastFrame)⟩
    have continued : Evaluates (.unit :: .word word :: environment)
        (middleStore.set cellLocation (.inRight .unit (.word word)))
        (((next.weakenAt 0).weakenAt 0).rename mapping.lift.lift) target finalStore := by
      rw [weakened_twice]
      exact tailEvaluated
    exact LanguageResult.bind_success _ valueEvaluated
      (Evaluates.letE (Evaluates.storeCell (.var targetFound) oldRead (.inRight (.var rfl)) written) continued)
  case assignFault =>
    intro sourceEnvironment name value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, binding, index, rfl, valueCompiled, _, _, _, _, _, rfl⟩ :=
      sequence_assign compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case expression =>
    intro sourceEnvironment value span rest initial middle final control evaluated _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, rfl, valueCompiled, unitType, nextCompiled, rfl⟩ :=
      sequence_expression compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [unitType] at valueRelated
    obtain rfl := unit_result valueRelated
    have nextEnvironment : EnvironmentRel world sourceEnvironment context.scope (fun index => 1 + mapping index)
        (.unit :: environment) := environmentRelated.prepend [.unit]
    have nextRuntime : EffectEnvironmentRel slots context.scope (fun index => 1 + mapping index)
        (.unit :: environment) := runtime.prepend [.unit]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        nextEnvironment nextRuntime middleState
    refine ⟨extension, target, finalStore, related, ?_, finalState, firstFrame.trans lastFrame⟩
    have continued : Evaluates (.unit :: environment) middleStore ((next.weakenAt 0).rename mapping.lift) target
        finalStore := by
      rw [weakened_once]
      exact tailEvaluated
    exact LanguageResult.bind_success _ valueEvaluated continued
  case expressionFault =>
    intro sourceEnvironment value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, rfl, valueCompiled, _, _, rfl⟩ := sequence_expression compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case compound =>
    intro sourceEnvironment statement rest initial middle final control headDerivation _ headSimulated
      tailSimulated fuel context inLoop code noFunctions eligible compiled world mapping environment store
      environmentRelated runtime stateRelated
    obtain ⟨previous, head, next, rfl, headLowered, nextCompiled, rfl⟩ :=
      sequence_compound (Compound.isCompound headDerivation) compiled
    obtain ⟨firstExtension, firstTarget, middleStore, firstRelated, firstEvaluated, middleState, firstFrame⟩ :=
      headSimulated noFunctions (eligible _ (List.mem_cons.mpr (.inl rfl))) headLowered environmentRelated runtime
        stateRelated
    cases firstRelated
    obtain ⟨extension, target, finalStore, related, nextEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        ((environmentRelated.extendWorld firstExtension).prepend
          [.unit, .inLeft resultType .unit, .inLeft LocalLoop.transferType (.inLeft resultType .unit)])
        (runtime.prepend [.unit, .inLeft resultType .unit, .inLeft LocalLoop.transferType (.inLeft resultType .unit)])
        middleState
    exact ⟨firstExtension ++ extension, target, finalStore, related, sequence_next firstEvaluated nextEvaluated,
      by simpa only [List.append_assoc] using finalState, firstFrame.trans lastFrame⟩
  case compoundStop =>
    intro sourceEnvironment statement rest initial final control headDerivation stopped headSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, head, next, rfl, headLowered, _, rfl⟩ :=
      sequence_compound (Compound.isCompound headDerivation) compiled
    obtain ⟨extension, target, finalStore, related, evaluated, finalState, frame⟩ :=
      headSimulated noFunctions (eligible _ (List.mem_cons.mpr (.inl rfl))) headLowered environmentRelated runtime
        stateRelated
    exact ⟨extension, target, finalStore, related, sequence_stopped related stopped evaluated, finalState, frame⟩
  case block =>
    intro sourceEnvironment body span initial final control _ innerSimulated
      fuel context inLoop head noFunctions eligible lowered world mapping environment store environmentRelated runtime
      stateRelated
    cases eligible with
    | block bodyEligible =>
    obtain ⟨_, sequenced⟩ := block_sequence bodyEligible lowered
    exact innerSimulated noFunctions bodyEligible sequenced environmentRelated runtime stateRelated
  case ifTrue =>
    intro sourceEnvironment condition body span initial middle final control word evaluated nonzero _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | ifThen _ bodyEligible =>
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, branchCompiled, rfl⟩ := lowered
    obtain ⟨wordType, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, middleStore, conditionRelated, conditionEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    rw [wordType] at conditionRelated
    obtain rfl := word_result conditionRelated
    obtain ⟨_, sequenced⟩ := block_sequence bodyEligible branchCompiled
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions bodyEligible sequenced (environmentRelated.prepend [.bool true])
        (runtime.prepend [.bool true]) middleState
    refine ⟨extension, target, finalStore, related, ?_, finalState, firstFrame.trans lastFrame⟩
    have flag : (!(word == Word.zero)) = true := by simpa using nonzero
    have tested := condition_evaluates (mapping := mapping) conditionEvaluated
    rw [flag] at tested
    rw [LocalLoop.conditional_rename]
    exact LocalControl.choose_true _ tested (by rw [renamed_weakened]; exact branchEvaluated)
  case ifFalse =>
    intro sourceEnvironment condition body span initial final evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, _, rfl⟩ := lowered
    obtain ⟨wordType, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, finalStore, conditionRelated, conditionEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    rw [wordType] at conditionRelated
    obtain rfl := word_result conditionRelated
    refine ⟨[], _, finalStore, .fallthrough, ?_, by simpa only [List.append_nil] using finalState, frame⟩
    have flag : (!(Word.zero == Word.zero)) = false := by decide
    have tested := condition_evaluates (mapping := mapping) conditionEvaluated
    rw [flag] at tested
    rw [LocalLoop.conditional_rename]
    exact LocalControl.choose_false _ tested (by
      simpa only [LocalLoop.weaken_zero, LocalLoop.fallthrough_rename] using
        LocalLoop.fallthrough_evaluates resultType (.bool false :: environment) finalStore)
  case ifFault =>
    intro sourceEnvironment condition body span initial final reason evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, _, rfl⟩ := lowered
    obtain ⟨_, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, finalStore, conditionRelated, conditionEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    cases conditionRelated with
    | language reasonWord =>
        refine ⟨[], _, finalStore, .language reasonWord, ?_, by simpa only [List.append_nil] using finalState, frame⟩
        rw [LocalLoop.conditional_rename]
        exact LocalControl.choose_failure _ (LanguageResult.bind_failure .bool conditionEvaluated)
  case switchCase =>
    intro sourceEnvironment value cases defaultBody span initial middle final control word body evaluated selected _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | switch _ literals arms _ =>
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, wordType, armsLowered, _, rfl⟩ := lowered
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨code, codeLowered, chain⟩ :=
      switch_selected (mapping := mapping) (environment := environment) armsLowered literals selected
    obtain ⟨arm, armMember, rfl⟩ := select_mem selected
    obtain ⟨_, sequenced⟩ := block_sequence (arms arm armMember) codeLowered
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions (arms arm armMember) sequenced (environmentRelated.prepend [.word word])
        (runtime.prepend [.word word]) middleState
    exact ⟨extension, target, finalStore, related, LanguageResult.bind_success _ valueEvaluated (chain branchEvaluated),
      finalState, firstFrame.trans lastFrame⟩
  case switchDefault =>
    intro sourceEnvironment value cases defaultBody span initial middle final control word evaluated unselected _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | switch _ literals _ defaults =>
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, wordType, armsLowered, defaultCompiled, rfl⟩ := lowered
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨_, sequenced⟩ := block_sequence defaults defaultCompiled
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions defaults sequenced (environmentRelated.prepend [.word word])
        (runtime.prepend [.word word]) middleState
    exact ⟨extension, target, finalStore, related, LanguageResult.bind_success _ valueEvaluated
      (switch_unselected armsLowered literals unselected branchEvaluated), finalState, firstFrame.trans lastFrame⟩
  case switchFault =>
    intro sourceEnvironment value cases defaultBody span initial final reason evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, _, _, _, rfl⟩ := lowered
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩

/-- An eligible block simulates its actual `lowerStatements` code. -/
theorem block_simulation (step : BuiltinStep model slots) {supported : String → Prop} {resultType : Core.Ty}
    {sourceEnvironment : Semantics.Environment} {body : List YulStmt} {initial final : YulSemantics.State}
    {control : Semantics.Control} (eligible : YulFragment.Eligible supported body)
    (executed : YulSemantics.Run sourceEnvironment body initial control final)
    {fuel : Nat} {scope : Scope} {signatures : List Signature} {code : Core.Expr}
    (compiled : YulLowering.lowerStatements fuel scope resultType body signatures = .ok code)
    {world : World} {mapping : Renaming} {environment : Environment} {store : Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (stateRelated : StateRel model world initial store) :
    ∃ extension target finalStore, ControlRel resultType control target ∧
      Evaluates environment store (code.rename mapping) target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨_, sequenced⟩ := statements_sequence eligible.2 compiled
  exact sequence_simulation (supported := supported) step executed rfl eligible.2 sequenced environmentRelated runtime
    stateRelated

end Simulation

/-- Effects whose assembly rule is the fragment's run meet the assembly
obligation once their builtins do. -/
theorem assembly_preserves {supported : String → Prop} {model : StateModel RuntimeCallEffectsSemantics.State}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State}
    (assembled : ∀ {functions environment body initial control final},
      effects.assembly functions environment body initial control final →
        YulSemantics.Run environment body initial control final)
    (step : BuiltinStep model slots) :
    DerivationCorrespondence.AssemblyPreservation supported model slots effects := by
  intro functions sourceEnvironment body initial control final eligible executed signatures codes locations captured span
  intro fuel scope result loops expression compiled _ world mapping environment store environmentRelated _ runtime
    stateRelated installed
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨extension, target, finalStore, related, evaluated, finalState, closures⟩ :=
        block_simulation step eligible (assembled executed) compiled environmentRelated runtime stateRelated
      exact ⟨extension, target, finalStore, related, evaluated, finalState, installed.preserved closures, closures⟩

end Solcore.Frontend.RustHull.YulBlockCorrespondence
