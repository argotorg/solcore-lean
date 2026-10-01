import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedParameterIndexed
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A static mixed-body receipt and an independent initializer-fault trace
retain the context before the failed declaration. Checked cached calls retain
ordered parameter/local cells, raw mapping metadata and real Core resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedLexicalNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalNamedBody

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_named", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed_named.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def absentNode : ExpressionNode := {
  id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id) }
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def innerStatements := [statement 0, statement 1]
private def scopedBlock : StatementNode := ⟨statement 3, span, .unit, .block innerStatements⟩
private def statements := [statement 3, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression absentNode, .statement first, .statement second, .statement returned, .statement scopedBlock] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial := SourceSemantics.Context.ofSignatures signatures
private def entered := initial.withLocal (binder 0).id (binder 0).scheme
private def complete := entered.withLocal (binder 1).id (binder 1).scheme
private theorem firstExtension : BinderExtends owner initial (binder 0) entered := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := .ofSignatures signatures, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner entered (binder 1) complete := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, entered, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem absentTyped : ExpressionHasType source entered expression .bool := by
  have admitted : TypeAdmissible entered .bool := .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _)
  apply ExpressionHasType.ofOrdinary (node := absentNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem absentSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := absentNode) rfl rfl))))))
private theorem innerSyntax : TypedLexicalControl.Syntax source initial false innerStatements .unit :=
  .uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide)
    (.initialized (node := second) (initializerNode := absentNode) rfl rfl rfl rfl secondExtension (by decide)
      rfl rfl absentTyped absentSyntax (.body (.nil (.inl rfl))))
private theorem syntaxTree : TypedLexicalControl.Syntax source initial true statements .unit :=
  .block (node := scopedBlock) rfl rfl rfl innerSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl))
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def compilation (plan : SourceSpecializationWorklist.Plan) : SourceCoreFunctions.Context := {
  plan, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) : SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation ⟨[]⟩ ⟨owner, []⟩ []
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Actual contextual success supplies both let receipts and the remaining
body tree. The static premises contain no child/body semantic theorem. -/
theorem lexical_certificate (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (sourceSignatures : initial.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (lowerBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    {fuel : Nat} {code : Expr} (fellThrough escaped : Word)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel
      source [] statements .unit (fun _ => Word.zero) fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts ⟨owner, []⟩ [] frame globals onError readFuel values source initial []
      (fun _ => Word.zero) [] statements .unit .unit
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel fellThrough escaped code) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan)
      (native := none) (parent := none) (skipInitializer := none) ?_ unique rfl rfl ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl lowerBinder rfl rfl rfl syntaxTree rfl accepted
  · constructor
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intros; rfl
    · intros; rfl
  · intro id declared index type selected authentic
    cases selected

private def closure : Dynamic.Closure := ⟨[], .unit, statements, source, [], initial, []⟩
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def faultHeap : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩

/-- A fault inside the block restores its enclosing context while retaining the
uninitialized cell. The failed declaration never enters the source environment. -/
theorem scoped_initializer_fault :
    Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements initial
      (.uninitializedLocation ⟨0⟩) faultHeap ∧
    FunctionCallBody.Trace program closure initial [] ⟨[]⟩ (.fault (.uninitializedLocation ⟨0⟩)) faultHeap ∧
    initial ≠ entered := by
  have inner : Dynamic.StatementsFault program initial [] source [] ⟨[]⟩ innerStatements entered
      (.uninitializedLocation ⟨0⟩) faultHeap := by
    apply Dynamic.StatementsFault.tail
      (Dynamic.StatementExecutes.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append)
    apply Dynamic.StatementsFault.head
    apply Dynamic.StatementFaults.letInitializer (node := second) (lookupStatement?_sound rfl) rfl rfl
    apply Dynamic.ExpressionFaults.form (node := absentNode) (lookupExpression?_sound rfl)
    exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
      rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)
  have failed : Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements initial
      (.uninitializedLocation ⟨0⟩) faultHeap :=
    .head (.block (lookupStatement?_sound rfl) rfl inner)
  refine ⟨failed, .fault failed, ?_⟩
  intro same
  have impossible : 0 = 1 := congrArg (fun context => context.locals.length) same
  omega

/-- Empty scoped branches at a Bool result do not acquire a false Unit fact. -/
theorem scoped_empty_bool :
    TypedLexicalControl.Syntax source initial false [] .bool ∧
    TypedScopedStatements.Executes false program initial [] source [] ⟨[]⟩ [] initial (.fallthrough []) ⟨[]⟩ :=
  ⟨.body (.nil (.inl rfl)), .control .nil⟩

private def unitBlock : StatementNode := ⟨statement 4, span, .unit, .block [statement 0]⟩
private def unitSource : TypedSource := {source with roots := [.statement (statement 4)], nodes := source.nodes ++ [.statement unitBlock]}
private theorem unitSyntax : TypedLexicalControl.Syntax unitSource initial true [statement 4] .unit :=
  .block (node := unitBlock) rfl rfl rfl
    (.uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide) (.body (.nil (.inl rfl))))
    (.body (.nil (.inr rfl)))
private theorem unitUnique : NodeOccurrencesUnique unitSource := by cbv; decide

/-- The source derivation allocates inside a false-mode block and restores the
outer environment/context. The function-mode Unit fact is derived, not supplied. -/
theorem unit_source_exit :
    Dynamic.FunctionStatementsExecute program initial [] unitSource [] ⟨[]⟩ [statement 4] initial (.fallthrough []) faultHeap ∧
    (let expected := TypeSystem.Ty.unit; expected = .unit) := by
  have executed : Dynamic.FunctionStatementsExecute program initial [] unitSource [] ⟨[]⟩ [statement 4] initial (.fallthrough []) faultHeap :=
    .singleton (lookupStatement?_sound rfl) (by intro expression; simp [unitBlock])
      (.block (node := unitBlock) (lookupStatement?_sound rfl) rfl
        (.cons (.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append) .nil))
  exact ⟨executed, true_fallthrough_unit unitSyntax unitUnique (.control executed)⟩

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function unit() { let outer: Word; { let inner = true; } }",
  "function nested(flag: Bool, raw: mapping(Bool => Bool)) returns (Bool) { let x = true; let m: mapping(Bool => Bool); if (flag) { let x = m[true]; { let y = !x; y; } } else { let x = !raw[false]; { let gap: Bool; x; } } let out = x; return out; }",
  "function shadow(flag: Bool) returns (Bool) { let x = flag; { let x = !flag; { let x = flag; x; } x; } return x; }",
  "function early(flag: Bool) returns (Bool) { let m: mapping(Bool => Bool); { let x = m[flag]; if (!x) { let hidden: Word; return !x; } } let unreachable = false; return false; }",
  "function conditionFault(flag: Bool) returns (Bool) { let gap: Bool; if (gap) { let skipped = flag; } return flag; }",
  "function branchFault(flag: Bool) returns (Bool) { let outer = flag; { let gap: Bool; if (flag) { let before = !outer; let failed = gap; } else { let skipped = outer; } } return outer; }",
  "function missing(flag: Bool) returns (Bool) { let m: mapping(Bool => Item); if (flag) { let gap: Word; let failed = m[flag]; } return false; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { { let alias = f; alias; } if (flag) { let same = f; return same; } return f; }"
]

private def finished (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initialState : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initialState
  let result ← SourceCoreUnifiedCorpusSupport.get "typed lexical named resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  pure result.observation

private def assertCells (initialState final : SourceTypedRuntime.RuntimeState)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
    s!"typed lexical named prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
    s!"typed lexical named ordered cells changed {name}: {reprStr final.heap}"

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (initialState : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    match ← finished compiled name arguments fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed lexical named result changed {name}"
      assertCells initialState final cells name
      SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"typed lexical named unsafe final heap {name}"
    | other => throw (IO.userError s!"typed lexical named failed {name}: {reprStr other}")

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name localName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "typed lexical named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "typed lexical named exact binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed lexical named bodies" content
    ["unit", "nested", "shadow", "early", "conditionFault", "branchFault", "missing", "identity", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  let yes : SourceTypedRuntime.Value := .bool true
  let no : SourceTypedRuntime.Value := .bool false
  check compiled "unit" [] .unit [(.word, none), (.bool, some yes)] initialState
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .bool) .bool []
  let emptyMap : SourceTypedRuntime.Value := .mapping .bool .bool []
  check compiled "nested" [yes, rawMap] yes
    [(.bool, some yes), (.mapping .bool .bool, some rawMap), (.bool, some yes),
      (.mapping .bool .bool, some emptyMap), (.bool, some no), (.bool, some yes), (.bool, some yes)] initialState
  check compiled "nested" [no, rawMap] yes
    [(.bool, some no), (.mapping .bool .bool, some rawMap), (.bool, some yes),
      (.mapping .bool .bool, none), (.bool, some yes), (.bool, none), (.bool, some yes)] initialState
  check compiled "shadow" [no] no
    [(.bool, some no), (.bool, some no), (.bool, some yes), (.bool, some no)] initialState
  check compiled "early" [no] yes
    [(.bool, some no), (.mapping .bool .bool, some emptyMap), (.bool, some no), (.word, none)] initialState
  check compiled "branchFault" [no] no
    [(.bool, some no), (.bool, some no), (.bool, none), (.bool, some no)] initialState
  let item ← SourceCoreUnifiedCorpusSupport.get "typed lexical named Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
  check compiled "missing" [no] no [(.bool, some no), (.mapping .bool (.nominal item.id []), none)] initialState
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let fn : SourceTypedRuntime.Value := .global identity []
  check compiled "callable" [fn, yes] fn
    [(.function .bool .bool, some fn), (.bool, some yes), (.function .bool .bool, some fn), (.function .bool .bool, some fn)] initialState
  check compiled "callable" [fn, no] fn
    [(.function .bool .bool, some fn), (.bool, some no), (.function .bool .bool, some fn)] initialState
  for name in ["conditionFault", "branchFault"] do
    let gap ← faultBinder compiled name "gap"
    for fuel in [0, 41, 300000] do
      match ← finished compiled name [yes] fuel initialState with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"lexical fault changed its exact binder {name}"
        let cells := if name == "conditionFault" then [(.bool, some yes), (.bool, none)]
          else [(.bool, some yes), (.bool, some yes), (.bool, none), (.bool, some no)]
        assertCells initialState final cells name
      | other => throw (IO.userError s!"typed lexical named initializer/condition fault changed: {reprStr other}")
  for fuel in [0, 41, 300000] do
    match ← finished compiled "missing" [yes] fuel initialState with
    | .fault (.typeMismatch raw none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "lexical missing-default raw nominal metadata changed"
      assertCells initialState final
        [(.bool, some yes), (.mapping .bool raw, some (.mapping .bool raw [])), (.word, none)] "missing"
    | other => throw (IO.userError s!"typed lexical named missing default changed: {reprStr other}")
  IO.println "typed lexical named bodies: scoped bindings/return/fault, actual parameter order, raw mapping metadata and resume GREEN"

end Tests.SourceCoreTypedLexicalNamedParameters
