import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Internal.CallGraphs

/-!
# Profiles: aggregates

The profiles `runtime-aggregates` and `runtime-aggregate-call-graphs`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.AggregateDAG
/-! Checked Word-function graphs with immutable Word pairs and Word sums.
Aggregates are internal values: helper arguments/results and ABI values remain
Words, and private cells can contain only Words. Case branches bind one payload
Word before every existing local, including Unit and cell bindings. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Aggregates

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-aggregate-dag-v1"

inductive Target where
  | word | bool | unit | wordPair | wordSum
  deriving Repr, BEq, DecidableEq

inductive Local where
  | word | bool | cellWord | unit | wordPair | wordSum
  deriving Repr, BEq, DecidableEq

def Target.toLocal : Target → Local
  | .word => .word
  | .bool => .bool
  | .unit => .unit
  | .wordPair => .wordPair
  | .wordSum => .wordSum

def Local.toTarget? : Local → Option Target
  | .word => some .word
  | .bool => some .bool
  | .unit => some .unit
  | .wordPair => some .wordPair
  | .wordSum => some .wordSum
  | .cellWord => none

private def scalarLocal : Solcore.Synthesis.Core.Target → Local
  | .word => .word
  | .bool => .bool

private def require (actual expected : Local) : Option Unit :=
  if actual == expected then some () else none

private def inferLocal? (locals : List Local) (priorFunctions : Nat) : Expr → Option Local
  | .word _ => some .word
  | .bool _ => some .bool
  | .unit => some .unit
  | .var index => do
      let kind ← locals[index]?
      if kind == .cellWord then none else some kind
  | .letE initializer body => do
      let kind ← inferLocal? locals priorFunctions initializer
      let result ← inferLocal? (kind :: locals) priorFunctions body
      if result == .cellWord then none else some result
  | .ifE condition yes no => do
      require (← inferLocal? locals priorFunctions condition) .bool
      let left ← inferLocal? locals priorFunctions yes
      let right ← inferLocal? locals priorFunctions no
      if left == right && left != .cellWord then some left else none
  | .pair left right => do
      require (← inferLocal? locals priorFunctions left) .word
      require (← inferLocal? locals priorFunctions right) .word
      return .wordPair
  | .first operand | .second operand => do
      require (← inferLocal? locals priorFunctions operand) .wordPair
      return .word
  | .inLeft .word payload | .inRight .word payload => do
      require (← inferLocal? locals priorFunctions payload) .word
      return .wordSum
  | .caseE scrutinee left right => do
      require (← inferLocal? locals priorFunctions scrutinee) .wordSum
      let leftResult ← inferLocal? (.word :: locals) priorFunctions left
      let rightResult ← inferLocal? (.word :: locals) priorFunctions right
      if leftResult == rightResult && leftResult != .cellWord then some leftResult else none
  | .unary operation operand => do
      match operation with
      | .integerNot | .integerToWord | .wordToInteger => none
      | _ =>
        require (← inferLocal? locals priorFunctions operand)
          (scalarLocal (Solcore.Synthesis.Core.Target.unaryOperand operation))
        return scalarLocal (Solcore.Synthesis.Core.Target.unaryResult operation)
  | .binary operation left right => do
      match operation with
      | .integerAdd | .integerSub | .integerMul | .integerDiv | .integerMod
      | .integerEq | .integerLt | .integerAnd | .integerOr | .integerXor => none
      | _ =>
        require (← inferLocal? locals priorFunctions left) .word
        require (← inferLocal? locals priorFunctions right) .word
        return scalarLocal (Solcore.Synthesis.Core.Target.binaryResult operation)
  | .ternary _ first second third => do
      require (← inferLocal? locals priorFunctions first) .word
      require (← inferLocal? locals priorFunctions second) .word
      require (← inferLocal? locals priorFunctions third) .word
      return .word
  | .apply (.var index) argument => do
      if locals.length ≤ index && index < locals.length + priorFunctions then
        require (← inferLocal? locals priorFunctions argument) .word
        return .word
      else none
  | .newCell .word initializer => do
      require (← inferLocal? locals priorFunctions initializer) .word
      return .cellWord
  | .loadCell (.var index) => do
      require (← locals[index]?) .cellWord
      return .word
  | .storeCell (.var index) value => do
      require (← locals[index]?) .cellWord
      require (← inferLocal? locals priorFunctions value) .word
      return .unit
  | _ => none

/-- Only a syntactically direct Word allocation can produce `cellWord`.
Unit bindings remain present in the context even when source printing elides them. -/
def initializerKind? (locals : List Local) (priorFunctions : Nat) (expression : Expr) : Option Local :=
  inferLocal? locals priorFunctions expression

/-- An expression cannot return a cell. The sole cell introduction position is
the initializer of a let, where `initializerKind?` supplies its local tag. -/
def infer? (locals : List Local) (priorFunctions : Nat) (expression : Expr) : Option Target := do
  (← inferLocal? locals priorFunctions expression).toTarget?

def acceptsAt (locals : List Local) (priorFunctions : Nat) (target : Target) (expression : Expr) : Bool :=
  infer? locals priorFunctions expression == some target

def features : Expr → List String
  | .word _ => ["wordLiteral"]
  | .bool _ => ["boolLiteral"]
  | .unit => ["unitLiteral"]
  | .var _ => ["local"]
  | .letE initializer body => "let" :: features initializer ++ features body
  | .ifE condition yes no => "if" :: features condition ++ features yes ++ features no
  | .pair left right => "pair" :: features left ++ features right
  | .first operand => "first" :: features operand
  | .second operand => "second" :: features operand
  | .inLeft .word payload => "inLeft" :: features payload
  | .inRight .word payload => "inRight" :: features payload
  | .caseE scrutinee left right => "case" :: features scrutinee ++ features left ++ features right
  | .unary operation operand => ("unary:" ++ reprStr operation) :: features operand
  | .binary operation left right => ("binary:" ++ reprStr operation) :: features left ++ features right
  | .ternary operation first second third =>
      ("ternary:" ++ reprStr operation) :: features first ++ features second ++ features third
  | .apply (.var _) argument => "functionCall" :: features argument
  | .newCell .word initializer => "newCell" :: features initializer
  | .loadCell (.var _) => ["loadCell"]
  | .storeCell (.var _) value => "storeCell" :: features value
  | _ => []

def helpersAccepted (helpers : List Expr) : Bool :=
  helpers.zipIdx.all fun (body, index) => acceptsAt [.word] index .word body

structure CheckedDAG where private mk ::
  helpers : List Expr
  entry : Expr
  count : 1 ≤ helpers.length ∧ helpers.length ≤ 3
  helperScopes : helpersAccepted helpers = true
  entryScope : acceptsAt [.word] helpers.length .word entry = true
  checked : (functionDAGProgram helpers entry).check = true

namespace CheckedDAG

def program (graph : CheckedDAG) : Program := functionDAGProgram graph.helpers graph.entry

def features (graph : CheckedDAG) : List String :=
  graph.helpers.flatMap Aggregates.features ++ Aggregates.features graph.entry

def ofParts? (helpers : List Expr) (entry : Expr) : Option CheckedDAG :=
  if count : 1 ≤ helpers.length ∧ helpers.length ≤ 3 then
    if helperScopes : helpersAccepted helpers = true then
      if entryScope : acceptsAt [.word] helpers.length .word entry = true then
        if checked : (functionDAGProgram helpers entry).check = true then
          some ⟨helpers, entry, count, helperScopes, entryScope, checked⟩
        else none
      else none
    else none
  else none

private def parts? : Expr → Option (List Expr × Expr)
  | .lambda .word .word entry => some ([], entry)
  | .letE (.lambda .word .word helper) rest => do
      let (helpers, entry) ← parts? rest
      return (helper :: helpers, entry)
  | _ => none

def ofProgram? : Program → Option CheckedDAG
  | {resultType := .function .word .word, dataDefinitions := [], body} => do
      let (helpers, entry) ← parts? body
      ofParts? helpers entry
  | _ => none

theorem wellTyped (graph : CheckedDAG) : graph.program.WellTyped :=
  Program.check_full_sound graph.checked

def instantiate (graph : CheckedDAG) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply graph.program.body (.word input)
}

theorem instantiate_wellTyped (graph : CheckedDAG) (input : Word) :
    (graph.instantiate input).WellTyped := by
  refine ⟨graph.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply graph.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (graph : CheckedDAG) (input : Word) :
    (graph.instantiate input).check = true :=
  Program.check_complete (graph.instantiate_wellTyped input)

end CheckedDAG
end Solcore.Synthesis.Core.Aggregates

namespace Solcore.Synthesis.Core
abbrev CheckedAggregateDAG := Aggregates.CheckedDAG
end Solcore.Synthesis.Core
end

section
-- leanmerge: from Solcore.Synthesis.Core.AggregateCallGraph
/-! Direct, bounded generation of typed expressions that compose immutable Word
pairs, Word sums, projections and case payload scopes with acyclic helper calls.
Helper arguments and results remain Words. The original Core graph is sealed by
the existing aggregate DAG checker; no evaluator or source result is an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.AggregateCallGraph

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-aggregate-call-graph-grammar-v1/" ++ Seed.algorithmId

structure Request where
  seed : Seed
  maxProgramNodes : Nat
  deriving Repr, BEq, DecidableEq

inductive Error where
  | budgetTooSmall
  | budgetTooLarge
  | checkerInvariant
  | budgetInvariant
  deriving Repr, BEq, DecidableEq

def shapeVersion : String := "core-aggregate-call-graph-shapes-v1"

def shapeCatalog : List String :=
  ["pair-component-call", "sum-payload-call", "projected-call-argument", "case-scrutinee-call",
   "case-branch-call", "payload-call-argument", "aggregate-let", "aggregate-branch", "nested-case"]

/-- Shapes in which a helper call and an aggregate value or payload scope meet. -/
def callCompositionShapes : List String := shapeCatalog.take 6

private def hasCall (expression : Expr) : Bool :=
  (Aggregates.features expression).contains "functionCall"

private def projects (expression : Expr) : Bool :=
  let features := Aggregates.features expression
  features.contains "first" || features.contains "second"

private def references (indices : List Nat) : Expr → Bool
  | .var index => indices.contains index
  | .letE initializer body =>
      references indices initializer || references (indices.map (· + 1)) body
  | .caseE scrutinee left right =>
      references indices scrutinee || references (indices.map (· + 1)) left ||
        references (indices.map (· + 1)) right
  | .ifE first second third | .ternary _ first second third =>
      references indices first || references indices second || references indices third
  | .binary _ left right | .pair left right | .apply left right =>
      references indices left || references indices right
  | .unary _ operand | .first operand | .second operand | .inLeft _ operand | .inRight _ operand =>
      references indices operand
  | _ => false

/-- Occurrences in one body. `payloads` holds the current indices of every
enclosing case payload; `inCase` records whether a case branch encloses it. -/
private def occurrences (locals : List Aggregates.Local) (prior : Nat) (payloads : List Nat) (inCase : Bool) :
    Expr → List String
  | .letE initializer body =>
      let kind := Aggregates.initializerKind? locals prior initializer
      (if kind == some .wordPair || kind == some .wordSum then ["aggregate-let"] else []) ++
        occurrences locals prior payloads inCase initializer ++
        (match kind with
          | some kind => occurrences (kind :: locals) prior (payloads.map (· + 1)) inCase body
          | none => [])
  | .ifE condition yes no =>
      let result := Aggregates.infer? locals prior (.ifE condition yes no)
      (if result == some .wordPair || result == some .wordSum then ["aggregate-branch"] else []) ++
        occurrences locals prior payloads inCase condition ++
        occurrences locals prior payloads inCase yes ++ occurrences locals prior payloads inCase no
  | .caseE scrutinee left right =>
      let inner := 0 :: payloads.map (· + 1)
      (if hasCall scrutinee then ["case-scrutinee-call"] else []) ++
        (if hasCall left || hasCall right then ["case-branch-call"] else []) ++
        (if inCase then ["nested-case"] else []) ++
        occurrences locals prior payloads inCase scrutinee ++
        occurrences (.word :: locals) prior inner true left ++
        occurrences (.word :: locals) prior inner true right
  | .pair left right =>
      (if hasCall left || hasCall right then ["pair-component-call"] else []) ++
        occurrences locals prior payloads inCase left ++ occurrences locals prior payloads inCase right
  | .inLeft _ payload | .inRight _ payload =>
      (if hasCall payload then ["sum-payload-call"] else []) ++
        occurrences locals prior payloads inCase payload
  | .apply function argument =>
      (if projects argument then ["projected-call-argument"] else []) ++
        (if references payloads argument then ["payload-call-argument"] else []) ++
        occurrences locals prior payloads inCase function ++
        occurrences locals prior payloads inCase argument
  | .ternary _ first second third =>
      occurrences locals prior payloads inCase first ++ occurrences locals prior payloads inCase second ++
        occurrences locals prior payloads inCase third
  | .binary _ left right =>
      occurrences locals prior payloads inCase left ++ occurrences locals prior payloads inCase right
  | .unary _ operand | .first operand | .second operand =>
      occurrences locals prior payloads inCase operand
  | _ => []

/-- Syntactic composition shapes over every declared helper body and the entry,
in catalog order. They do not claim that a branch, call or payload executes. -/
def structuralShapes (graph : Aggregates.CheckedDAG) : List String :=
  let found := (graph.helpers.zipIdx.flatMap fun (body, index) => occurrences [.word] index [] false body) ++
    occurrences [.word] graph.helpers.length [] false graph.entry
  shapeCatalog.filter found.contains

/-- The profile grammar: no private cells or Unit values, which the older
aggregate profile covers, and only direct calls to earlier helpers. -/
def withinGrammar : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => withinGrammar initializer && withinGrammar body
  | .ifE first second third | .ternary _ first second third | .caseE first second third =>
      withinGrammar first && withinGrammar second && withinGrammar third
  | .binary _ left right | .pair left right => withinGrammar left && withinGrammar right
  | .unary _ operand | .first operand | .second operand | .inLeft .word operand | .inRight .word operand =>
      withinGrammar operand
  | .apply (.var _) argument => withinGrammar argument
  | _ => false

def graphWithinGrammar (graph : Aggregates.CheckedDAG) : Bool :=
  graph.helpers.all withinGrammar && withinGrammar graph.entry

/-- The applied skeleton is the same as for scalar call graphs. -/
def minimumAppliedNodes (helperCount : Nat) : Nat := CallGraph.minimumAppliedNodes helperCount

def appliedOverhead (helperCount : Nat) : Nat := CallGraph.appliedOverhead helperCount

structure Generated where private mk ::
  initialSeed : Seed
  finalSeed : Seed
  maxProgramNodes : Nat
  bodyBudgets : List Nat
  function : Aggregates.CheckedDAG
  bounded : programNodes (function.instantiate Word.zero) ≤ maxProgramNodes

namespace Generated

def nodeCount (generated : Generated) : Nat :=
  programNodes (generated.function.instantiate Word.zero)

end Generated

private def choose := CallGraph.choose

/-- A typed leaf costs one node when it is a literal Word or Bool, or a local of
the requested kind; constructed pair and sum leaves cost three. -/
def leafCost (locals : List Aggregates.Local) : Aggregates.Target → Nat
  | .wordPair => if locals.contains .wordPair then 1 else 3
  | .wordSum => if locals.contains .wordSum then 1 else 3
  | _ => 1

private def indicesOf (locals : List Aggregates.Local) (kind : Aggregates.Local) : List Nat :=
  locals.zipIdx.filterMap fun (present, index) => if present == kind then some index else none

private def wordLeaf (locals : List Aggregates.Local) (seed : Seed) : Expr × Seed :=
  let indices := indicesOf locals .word
  let (kind, seed) := choose seed 3
  if !indices.isEmpty && kind < 2 then
    let (selected, seed) := choose seed indices.length
    (.var (indices[selected]?.getD 0), seed)
  else
    let (value, seed) := CallGraph.drawWord seed
    (.word value, seed)

/-- Literal aggregate leaves are chosen only when their three nodes fit. -/
private def leaf (target : Aggregates.Target) (locals : List Aggregates.Local) (budget : Nat) (seed : Seed) : Expr × Seed :=
  match target with
  | .bool =>
      let (value, seed) := choose seed 2
      (.bool (value == 1), seed)
  | .wordPair | .wordSum =>
      let kind := target.toLocal
      let indices := indicesOf locals kind
      let (useLocal, seed) := choose seed 2
      if !indices.isEmpty && (useLocal == 0 || budget < 3) then
        let (selected, seed) := choose seed indices.length
        (.var (indices[selected]?.getD 0), seed)
      else
        let (first, seed) := wordLeaf locals seed
        if target == .wordPair then
          let (second, seed) := wordLeaf locals seed
          (.pair first second, seed)
        else
          let (side, seed) := choose seed 2
          (if side == 0 then .inLeft .word first else .inRight .word first, seed)
  | _ => wordLeaf locals seed

private inductive Form where
  | leaf | unary | binary | ternary | letE | ifE | call | project | caseE | construct

/-- Partition `total` among children with the given minimum budgets. -/
private def partitionMin : List Nat → Nat → Seed → List Nat × Seed
  | [], _, seed => ([], seed)
  | [minimum], total, seed => ([max minimum total], seed)
  | minimum :: rest, total, seed =>
      let spare := total - (minimum :: rest).sum
      let (extra, seed) := choose seed (spare + 1)
      let (remaining, seed) := partitionMin rest (total - (minimum + extra)) seed
      ((minimum + extra) :: remaining, seed)

def letKinds : List Aggregates.Local := [.word, .wordPair, .wordPair, .wordSum, .wordSum]

private def letFits (locals : List Aggregates.Local) (target : Aggregates.Target) (budget : Nat) (kind : Aggregates.Local) : Bool :=
  match kind.toTarget? with
  | some initial => 1 + leafCost locals initial + leafCost (kind :: locals) target ≤ budget
  | none => false

/-- Only forms whose typed minimum fits are sampled. Word contexts weight the
aggregate consumers and calls so that their compositions are common. -/
private def forms (target : Aggregates.Target) (locals : List Aggregates.Local) (prior budget : Nat) : List Form :=
  let caseFits := 1 + leafCost locals .wordSum + 2 * leafCost (.word :: locals) target ≤ budget
  let ifFits := 2 + 2 * leafCost locals target ≤ budget
  let canLet := letKinds.any (letFits locals target budget)
  [.leaf] ++ (if canLet then [.letE] else []) ++ (if ifFits then [.ifE] else []) ++
    (if caseFits then [.caseE, .caseE] else []) ++
    match target with
    | .word =>
        (if budget ≥ 2 then [.unary] else []) ++ (if budget ≥ 3 then [.binary, .binary] else []) ++
        (if budget ≥ 4 then [.ternary] else []) ++ (if canLet then [.letE] else []) ++
        (if prior > 0 && budget ≥ 3 then [.call, .call] else []) ++
        (if 1 + leafCost locals .wordPair ≤ budget then [.project, .project] else [])
    | .bool => (if budget ≥ 2 then [.unary] else []) ++ (if budget ≥ 3 then [.binary, .binary] else [])
    | .wordPair | .wordSum => if budget ≥ 3 then [.construct, .construct] else []
    | .unit => []

/-- Structural fuel is independent of the node budget. Every body starts with
its Word parameter; let and case payloads extend the typed local context. -/
private def expression : Nat → Aggregates.Target → List Aggregates.Local → Nat → Nat → Seed → Expr × Seed
  | 0, target, locals, _, budget, seed => leaf target locals budget seed
  | fuel + 1, target, locals, prior, budget, seed =>
      let available := forms target locals prior budget
      let (selected, seed) := choose seed available.length
      match available[selected]?.getD .leaf with
      | .leaf => leaf target locals budget seed
      | .unary =>
          let (selected, seed) := choose seed (if target == .word then CallGraph.wordUnary.length else 1)
          let operation := if target == .word then CallGraph.wordUnary[selected]?.getD .wordNot else .boolNot
          let (operand, seed) := expression fuel target locals prior (budget - 1) seed
          (.unary operation operand, seed)
      | .binary =>
          let operations := if target == .word then CallGraph.wordBinary else CallGraph.boolBinary
          let (selected, seed) := choose seed operations.length
          let operation := operations[selected]?.getD (if target == .word then .wordAdd else .wordEq)
          let (budgets, seed) := partitionMin [1, 1] (budget - 1) seed
          let (left, seed) := expression fuel .word locals prior (budgets[0]?.getD 1) seed
          let (right, seed) := expression fuel .word locals prior (budgets[1]?.getD 1) seed
          (.binary operation left right, seed)
      | .ternary =>
          let (selected, seed) := choose seed 2
          let operation := if selected == 0 then TernaryOp.wordAddMod else .wordMulMod
          let (budgets, seed) := partitionMin [1, 1, 1] (budget - 1) seed
          let (first, seed) := expression fuel .word locals prior (budgets[0]?.getD 1) seed
          let (second, seed) := expression fuel .word locals prior (budgets[1]?.getD 1) seed
          let (third, seed) := expression fuel .word locals prior (budgets[2]?.getD 1) seed
          (.ternary operation first second third, seed)
      | .letE =>
          let kinds := letKinds.filter (letFits locals target budget)
          let (selected, seed) := choose seed kinds.length
          let kind := kinds[selected]?.getD .word
          let initial := (kind.toTarget?).getD .word
          let (budgets, seed) := partitionMin
            [leafCost locals initial, leafCost (kind :: locals) target] (budget - 1) seed
          let (value, seed) := expression fuel initial locals prior (budgets[0]?.getD 1) seed
          let (body, seed) := expression fuel target (kind :: locals) prior (budgets[1]?.getD 1) seed
          (.letE value body, seed)
      | .ifE =>
          let (budgets, seed) := partitionMin
            [1, leafCost locals target, leafCost locals target] (budget - 1) seed
          let (condition, seed) := expression fuel .bool locals prior (budgets[0]?.getD 1) seed
          let (yes, seed) := expression fuel target locals prior (budgets[1]?.getD 1) seed
          let (no, seed) := expression fuel target locals prior (budgets[2]?.getD 1) seed
          (.ifE condition yes no, seed)
      | .call =>
          let (callee, seed) := choose seed prior
          let (argument, seed) := expression fuel .word locals prior (budget - 2) seed
          (.apply (.var (locals.length + callee)) argument, seed)
      | .project =>
          let (side, seed) := choose seed 2
          let (operand, seed) := expression fuel .wordPair locals prior (budget - 1) seed
          (if side == 0 then .first operand else .second operand, seed)
      | .caseE =>
          let branch := leafCost (.word :: locals) target
          let (budgets, seed) := partitionMin [leafCost locals .wordSum, branch, branch] (budget - 1) seed
          let (scrutinee, seed) := expression fuel .wordSum locals prior (budgets[0]?.getD 1) seed
          let (left, seed) := expression fuel target (.word :: locals) prior (budgets[1]?.getD 1) seed
          let (right, seed) := expression fuel target (.word :: locals) prior (budgets[2]?.getD 1) seed
          (.caseE scrutinee left right, seed)
      | .construct =>
          if target == .wordPair then
            let (budgets, seed) := partitionMin [1, 1] (budget - 1) seed
            let (left, seed) := expression fuel .word locals prior (budgets[0]?.getD 1) seed
            let (right, seed) := expression fuel .word locals prior (budgets[1]?.getD 1) seed
            (.pair left right, seed)
          else
            let (side, seed) := choose seed 2
            let (payload, seed) := expression fuel .word locals prior (budget - 2) seed
            (if side == 0 then .inLeft .word payload else .inRight .word payload, seed)

/-- Generate the complete graph directly and validate it with the existing
aggregate DAG checker and full Core checker. Input sensitivity and composition
filters belong to Cases. -/
def generate (request : Request) : Except Error Generated := do
  if request.maxProgramNodes > 512 then throw .budgetTooLarge
  let counts := [1, 2, 3].filter (minimumAppliedNodes · ≤ request.maxProgramNodes)
  if counts.isEmpty then throw .budgetTooSmall
  let (selected, seed) := choose request.seed counts.length
  let count := counts[selected]?.getD 1
  let (budgets, seed) := partitionMin (List.replicate (count + 1) 1)
    (request.maxProgramNodes - appliedOverhead count) seed
  let mut seed := seed
  let mut helpers : List Expr := []
  for index in List.range count do
    let budget := budgets[index]?.getD 1
    let (body, next) := expression budget .word [.word] index budget seed
    helpers := helpers ++ [body]
    seed := next
  let budget := budgets[count]?.getD 1
  let (entry, finalSeed) := expression budget .word [.word] count budget seed
  let some function := Aggregates.CheckedDAG.ofParts? helpers entry | throw .checkerInvariant
  if bounded : programNodes (function.instantiate Word.zero) ≤ request.maxProgramNodes then
    return ⟨request.seed, finalSeed, request.maxProgramNodes, budgets, function, bounded⟩
  else throw .budgetInvariant

end Solcore.Synthesis.Core.AggregateCallGraph
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateCallGraphRenderer
/-! Source rendering of immutable Word pairs, Word sums, projections and case
payload scopes composed with calls to earlier named Word helpers. Scalar
operations, raw primitive aliases, operand snapshots and calls use exactly the
call-graph formatting; aggregate values use the tuple, sum and match forms of
the aggregate profile. This tested printer does not assert meaning preservation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateCallGraphRenderer

open Solcore.Core.Wire

/-- Every Core binder is named; helper indices follow this complete context. -/
inductive Binding where
  | word (name : String)
  | bool (name : String)
  | wordPair (name : String)
  | wordSum (name : String)

def Binding.kind : Binding → Solcore.Synthesis.Core.Aggregates.Local
  | .word _ => .word
  | .bool _ => .bool
  | .wordPair _ => .wordPair
  | .wordSum _ => .wordSum

def Binding.name : Binding → String
  | .word name | .bool name | .wordPair name | .wordSum name => name

abbrev Target := Solcore.Synthesis.Core.Aggregates.Target
abbrev Rendered := ScalarRenderer.Rendered

private def scalar? : Target → Option Solcore.Synthesis.Core.Target
  | .word => some .word
  | .bool => some .bool
  | _ => none

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"
  | .wordPair => "(word, word)"
  | .wordSum => "sum<word, word>"
  | .unit => "unit"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"
  | .unit => ""

private def name (index : Nat) : String := "sc_v" ++ toString index

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[CallGraphRenderer.line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

private def binding (target : Target) (value : String) : Option Binding :=
  match target with
  | .word => some (.word value)
  | .bool => some (.bool value)
  | .wordPair => some (.wordPair value)
  | .wordSum => some (.wordSum value)
  | .unit => none

private def kinds (bindings : List Binding) : List Solcore.Synthesis.Core.Aggregates.Local :=
  bindings.map Binding.kind

/-- Bind the selected pair component through a single evaluation of the pair. -/
private def project (left : Bool) (indent : Nat) (rendered : Rendered) : Rendered :=
  let result := bindValue .word indent rendered.nextId "0"
  let first := "sc_p" ++ toString result.nextId
  let second := "sc_p" ++ toString (result.nextId + 1)
  ⟨rendered.lines ++ result.lines ++ [
    CallGraphRenderer.line indent ("match (" ++ rendered.value ++ ") {"),
    CallGraphRenderer.line (indent + 4) ("case (" ++ first ++ ", " ++ second ++ ") {"),
    CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ (if left then first else second) ++ ";"),
    CallGraphRenderer.line (indent + 4) "}", CallGraphRenderer.line indent "}"],
    result.value, result.nextId + 2⟩

private def inject (constructor : String) (indent : Nat) (rendered : Rendered) : Rendered :=
  let result := bindValue .wordSum indent rendered.nextId (constructor ++ "(" ++ rendered.value ++ ")")
  ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩

/-- Bindings are nearest first, as in the original Core function. Scalar and
call cases follow `CallGraphRenderer.renderWithFunctions` line for line. A
projection or sum scrutinee is evaluated once; only case payloads extend scope.
Branch-local computations remain inside their selected branch. -/
def render (functions : List String) (target : Target) (bindings : List Binding) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match bindings[index]? with
      | some bound =>
          if bound.kind == Solcore.Synthesis.Core.Aggregates.Target.toLocal target then
            .ok ⟨[], bound.name, nextId⟩
          else .error (.unsupportedExpression "local used at a different type")
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let some kind := Solcore.Synthesis.Core.Aggregates.infer? (kinds bindings) functions.length initializer |
        throw (.unsupportedExpression "unsupported local initializer")
      let value ← render functions kind bindings indent nextId initializer
      let bound := bindValue kind indent value.nextId value.value
      let some named := binding kind bound.value | throw (.unsupportedExpression "Unit local")
      let rest ← render functions target (named :: bindings) indent bound.nextId body
      return ⟨value.lines ++ bound.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions .bool bindings indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← render functions target bindings (indent + 4) result.nextId yes
      let fallback ← render functions target bindings (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [CallGraphRenderer.line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [CallGraphRenderer.line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"),
          CallGraphRenderer.line indent "} else {"] ++ fallback.lines ++
        [CallGraphRenderer.line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"),
          CallGraphRenderer.line indent "}"], result.value, fallback.nextId⟩
  | .unary operation operand => do
      let some scalarTarget := scalar? target | throw (.unsupportedExpression "non-scalar unary result")
      unless CallGraphRenderer.supportedUnary operation do throw (.unsupportedUnary operation)
      let value ← render functions (if operation == .boolNot then .bool else .word) bindings indent nextId operand
      let value := if operation == .wordClz then CallGraphRenderer.snapshot indent value else value
      let expression ← CallGraphRenderer.unaryValue operation value.value
      let result := CallGraphRenderer.bindValue scalarTarget indent value.nextId expression
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let some scalarTarget := scalar? target | throw (.unsupportedExpression "non-scalar binary result")
      unless CallGraphRenderer.supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← render functions .word bindings indent nextId left
      let first := if Source.supportedBinary operation then first else CallGraphRenderer.snapshot indent first
      let second ← render functions .word bindings indent first.nextId right
      let second := if Source.supportedBinary operation then second else CallGraphRenderer.snapshot indent second
      let expression ← CallGraphRenderer.binaryValue operation first.value second.value
      let result := CallGraphRenderer.bindValue scalarTarget indent second.nextId expression
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation first second third => do
      unless target == .word do throw (.unsupportedExpression "non-Word ternary result")
      let first := CallGraphRenderer.snapshot indent (← render functions .word bindings indent nextId first)
      let second := CallGraphRenderer.snapshot indent (← render functions .word bindings indent first.nextId second)
      let third := CallGraphRenderer.snapshot indent (← render functions .word bindings indent second.nextId third)
      let result := CallGraphRenderer.bindValue .word indent third.nextId
        (CallGraphRenderer.ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .apply (.var index) argument => do
      unless target == .word do throw (.unsupportedExpression "apply")
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let value := CallGraphRenderer.snapshot indent (← render functions .word bindings indent nextId argument)
      let result := CallGraphRenderer.bindValue .word indent value.nextId (callee ++ "(" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .pair left right => do
      unless target == .wordPair do throw (.unsupportedExpression "pair")
      let first ← render functions .word bindings indent nextId left
      let second ← render functions .word bindings indent first.nextId right
      let result := bindValue .wordPair indent second.nextId ("(" ++ first.value ++ ", " ++ second.value ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .first operand => do
      unless target == .word do throw (.unsupportedExpression "projection")
      return project true indent (← render functions .wordPair bindings indent nextId operand)
  | .second operand => do
      unless target == .word do throw (.unsupportedExpression "projection")
      return project false indent (← render functions .wordPair bindings indent nextId operand)
  | .inLeft .word payload => do
      unless target == .wordSum do throw (.unsupportedExpression "inLeft")
      return inject "inl" indent (← render functions .word bindings indent nextId payload)
  | .inRight .word payload => do
      unless target == .wordSum do throw (.unsupportedExpression "inRight")
      return inject "inr" indent (← render functions .word bindings indent nextId payload)
  | .caseE scrutinee left right => do
      let tested ← render functions .wordSum bindings indent nextId scrutinee
      let result := bindValue target indent tested.nextId (zero target)
      let leftPayload := "sc_p" ++ toString result.nextId
      let selected ← render functions target (.word leftPayload :: bindings) (indent + 8) (result.nextId + 1) left
      let rightPayload := "sc_p" ++ toString selected.nextId
      let fallback ← render functions target (.word rightPayload :: bindings) (indent + 8) (selected.nextId + 1) right
      return ⟨tested.lines ++ result.lines ++ [CallGraphRenderer.line indent ("match (" ++ tested.value ++ ") {"),
        CallGraphRenderer.line (indent + 4) ("case inl(" ++ leftPayload ++ ") {")] ++ selected.lines ++
        [CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ selected.value ++ ";"),
          CallGraphRenderer.line (indent + 4) "}",
          CallGraphRenderer.line (indent + 4) ("case inr(" ++ rightPayload ++ ") {")] ++ fallback.lines ++
        [CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ fallback.value ++ ";"),
          CallGraphRenderer.line (indent + 4) "}", CallGraphRenderer.line indent "}"],
        result.value, fallback.nextId⟩
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.AggregateCallGraphRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateCallGraphEmitter
/-! Emission of checked Word-function graphs that compose pairs, sums,
projections and case payload scopes with helper calls. Helpers keep their Core
declaration order and can call only earlier declarations; their arguments and
results remain Words. `ScalarMeaning.AggregateCallGraph.emit_source_meaning`
relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateCallGraph


def emitterVersion : String := "solcore-source-aggregate-call-graphs-v1"
def wrapperVersion : String := "solcore-word-aggregate-call-graphs-contract-v1"
def contractName : String := "SynthesizedAggregateCallGraphs"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAggregateCallGraphsDeploy"]
def runtimePath : List String := ["SynthesizedAggregateCallGraphsDeploy", "SynthesizedAggregateCallGraphs"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- Emit all helper bodies and the entry from the same checked Core graph.
Local temporaries are fresh within each function and cannot shadow helper names. -/
def emit (graph : Solcore.Synthesis.Core.Aggregates.CheckedDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateCallGraphRenderer.render names .word [.word "sc_input"] 8 0 graph.entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AggregateCallGraph
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateRenderer
/-! Immutable Word pairs and sums coexist with private mutable Word locals.
Operands are rendered in Core evaluation order. Projection operands and sum
scrutinees are evaluated once; only case payloads extend the Core context.
Scalar operations, including the raw primitive aliases and their operand
snapshots, use exactly the call-graph formatting helpers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core.Aggregates (Target Local)

/-- The G0 features this renderer renders: its scalar operations are
`CallGraphRenderer`'s, so every operator and form. -/
def support := CallGraphRenderer.support

inductive Binding where
  | word (name : String)
  | bool (name : String)
  | cellWord (name : String)
  | unit
  | wordPair (name : String)
  | wordSum (name : String)

def Binding.kind : Binding → Local
  | .word _ => .word
  | .bool _ => .bool
  | .cellWord _ => .cellWord
  | .unit => .unit
  | .wordPair _ => .wordPair
  | .wordSum _ => .wordSum

private def bindingFor (target : Target) (name : String) : Binding :=
  match target with
  | .word => .word name
  | .bool => .bool name
  | .unit => .unit
  | .wordPair => .wordPair name
  | .wordSum => .wordSum name

structure Rendered where
  lines : List String
  value : Option String
  nextId : Nat

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def name (index : Nat) : String := "sc_v" ++ toString index
private def cellName (index : Nat) : String := "sc_c" ++ toString index

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"
  | .unit => "unit"
  | .wordPair => "(word, word)"
  | .wordSum => "sum<word, word>"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"
  | .unit => ""
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    some (name nextId), nextId + 1⟩

def requireValue (rendered : Rendered) : Except EmitError String :=
  match rendered.value with
  | some value => .ok value
  | none => .error (.unsupportedExpression "Unit used as a scalar value")

private def scalarTarget : Target → Except EmitError Solcore.Synthesis.Core.Target
  | .word => .ok .word
  | .bool => .ok .bool
  | _ => .error (.unsupportedExpression "non-scalar primitive target")

private def fromScalar (rendered : ScalarRenderer.Rendered) : Rendered :=
  ⟨rendered.lines, some rendered.value, rendered.nextId⟩

private def scalar (target : Target) (operands : List String)
    (indent nextId : Nat) (expression : Expr) : Except EmitError Rendered := do
  return fromScalar (← ScalarRenderer.render (← scalarTarget target) operands indent nextId expression)

/-- A rendered scalar operand in the shared call-graph helper representation. -/
private def scalarValue (rendered : Rendered) : Except EmitError ScalarRenderer.Rendered := do
  return ⟨rendered.lines, ← requireValue rendered, rendered.nextId⟩

private def cell (bindings : List Binding) (index : Nat) : Except EmitError String :=
  match bindings[index]? with
  | some (.cellWord name) => .ok name
  | _ => .error (.unsupportedExpression "cell reference is not a direct private local")

/-- The context includes every Core binder, including elided Unit values.
Helper function indices begin immediately after this complete local context. -/
def render (functions : List String) (target : Target) (bindings : List Binding)
    (indent nextId : Nat) : Expr → Except EmitError Rendered
  | .word value => scalar .word [] indent nextId (.word value)
  | .bool value => scalar .bool [] indent nextId (.bool value)
  | .unit => .ok ⟨[], none, nextId⟩
  | .var index => match bindings[index]? with
      | some (.word value) | some (.bool value)
      | some (.wordPair value) | some (.wordSum value) => .ok ⟨[], some value, nextId⟩
      | some .unit => .ok ⟨[], none, nextId⟩
      | _ => .error (.unboundLocal index)
  | .letE (.newCell .word initializer) body => do
      let initial ← render functions .word bindings indent nextId initializer
      let value ← requireValue initial
      let binding := cellName initial.nextId
      let rest ← render functions target (.cellWord binding :: bindings) indent (initial.nextId + 1) body
      return ⟨initial.lines ++ [line indent ("let " ++ binding ++ ": word = " ++ value ++ ";")] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .letE initializer body => do
      let some kind := Solcore.Synthesis.Core.Aggregates.infer?
          (bindings.map Binding.kind) functions.length initializer |
        throw (.unsupportedExpression "unsupported local initializer")
      let initial ← render functions kind bindings indent nextId initializer
      match kind with
      | .unit =>
        let rest ← render functions target (.unit :: bindings) indent initial.nextId body
        return ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩
      | .word | .bool | .wordPair | .wordSum =>
        let value ← requireValue initial
        let bound := bindValue kind indent initial.nextId value
        let binding := bindingFor kind (name initial.nextId)
        let rest ← render functions target (binding :: bindings) indent bound.nextId body
        return ⟨initial.lines ++ bound.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions .bool bindings indent nextId condition
      let conditionValue ← requireValue tested
      if target == .unit then
        let selected ← render functions .unit bindings (indent + 4) tested.nextId yes
        let fallback ← render functions .unit bindings (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line indent "} else {"] ++ fallback.lines ++ [line indent "}"],
          none, fallback.nextId⟩
      else
        let result := bindValue target indent tested.nextId (zero target)
        let resultValue ← requireValue result
        let selected ← render functions target bindings (indent + 4) result.nextId yes
        let selectedValue ← requireValue selected
        let fallback ← render functions target bindings (indent + 4) selected.nextId no
        let fallbackValue ← requireValue fallback
        return ⟨tested.lines ++ result.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line (indent + 4) (resultValue ++ " = " ++ selectedValue ++ ";"),
            line indent "} else {"] ++ fallback.lines ++
          [line (indent + 4) (resultValue ++ " = " ++ fallbackValue ++ ";"), line indent "}"],
          some resultValue, fallback.nextId⟩
  | .pair left right => do
      let first ← render functions .word bindings indent nextId left
      let firstValue ← requireValue first
      let second ← render functions .word bindings indent first.nextId right
      let secondValue ← requireValue second
      let result := bindValue .wordPair indent second.nextId
        ("(" ++ firstValue ++ ", " ++ secondValue ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .first operand => do
      let rendered ← render functions .wordPair bindings indent nextId operand
      let value ← requireValue rendered
      let result := bindValue .word indent rendered.nextId "0"
      let resultValue ← requireValue result
      let left := "sc_p" ++ toString result.nextId
      let right := "sc_p" ++ toString (result.nextId + 1)
      return ⟨rendered.lines ++ result.lines ++ [
        line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case (" ++ left ++ ", " ++ right ++ ") {"),
        line (indent + 8) (resultValue ++ " = " ++ left ++ ";"),
        line (indent + 4) "}", line indent "}"],
        result.value, result.nextId + 2⟩
  | .second operand => do
      let rendered ← render functions .wordPair bindings indent nextId operand
      let value ← requireValue rendered
      let result := bindValue .word indent rendered.nextId "0"
      let resultValue ← requireValue result
      let left := "sc_p" ++ toString result.nextId
      let right := "sc_p" ++ toString (result.nextId + 1)
      return ⟨rendered.lines ++ result.lines ++ [
        line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case (" ++ left ++ ", " ++ right ++ ") {"),
        line (indent + 8) (resultValue ++ " = " ++ right ++ ";"),
        line (indent + 4) "}", line indent "}"],
        result.value, result.nextId + 2⟩
  | .inLeft .word payload => do
      let rendered ← render functions .word bindings indent nextId payload
      let value ← requireValue rendered
      let result := bindValue .wordSum indent rendered.nextId ("inl(" ++ value ++ ")")
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .inRight .word payload => do
      let rendered ← render functions .word bindings indent nextId payload
      let value ← requireValue rendered
      let result := bindValue .wordSum indent rendered.nextId ("inr(" ++ value ++ ")")
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .caseE scrutinee yes no => do
      let tested ← render functions .wordSum bindings indent nextId scrutinee
      let value ← requireValue tested
      let result := if target == .unit then Rendered.mk [] none tested.nextId
        else bindValue target indent tested.nextId (zero target)
      let leftPayload := "sc_p" ++ toString result.nextId
      let selected ← render functions target (.word leftPayload :: bindings)
        (indent + 8) (result.nextId + 1) yes
      let rightPayload := "sc_p" ++ toString selected.nextId
      let fallback ← render functions target (.word rightPayload :: bindings)
        (indent + 8) (selected.nextId + 1) no
      let selectedLines ← match result.value with
        | none => pure selected.lines
        | some resultValue => do
          let selectedValue ← requireValue selected
          pure (selected.lines ++ [line (indent + 8) (resultValue ++ " = " ++ selectedValue ++ ";")])
      let fallbackLines ← match result.value with
        | none => pure fallback.lines
        | some resultValue => do
          let fallbackValue ← requireValue fallback
          pure (fallback.lines ++ [line (indent + 8) (resultValue ++ " = " ++ fallbackValue ++ ";")])
      return ⟨tested.lines ++ result.lines ++ [line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case inl(" ++ leftPayload ++ ") {")] ++ selectedLines ++
        [line (indent + 4) "}", line (indent + 4) ("case inr(" ++ rightPayload ++ ") {")] ++
        fallbackLines ++ [line (indent + 4) "}", line indent "}"], result.value, fallback.nextId⟩
  | .loadCell (.var index) => do
      return bindValue .word indent nextId (← cell bindings index)
  | .storeCell (.var index) value => do
      let reference ← cell bindings index
      let written ← render functions .word bindings indent nextId value
      let result ← requireValue written
      return ⟨written.lines ++ [line indent (reference ++ " = " ++ result ++ ";")], none, written.nextId⟩
  | .unary operation operand => do
      let result ← scalarTarget target
      unless CallGraphRenderer.supportedUnary operation do throw (.unsupportedUnary operation)
      let operandTarget := if operation == .boolNot then Target.bool else Target.word
      let value ← scalarValue (← render functions operandTarget bindings indent nextId operand)
      let value := if operation == .wordClz then CallGraphRenderer.snapshot indent value else value
      let bound := CallGraphRenderer.bindValue result indent value.nextId
        (← CallGraphRenderer.unaryValue operation value.value)
      return ⟨value.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .binary operation left right => do
      let result ← scalarTarget target
      unless CallGraphRenderer.supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← scalarValue (← render functions .word bindings indent nextId left)
      let first := if Source.supportedBinary operation then first else CallGraphRenderer.snapshot indent first
      let second ← scalarValue (← render functions .word bindings indent first.nextId right)
      let second := if Source.supportedBinary operation then second else CallGraphRenderer.snapshot indent second
      let bound := CallGraphRenderer.bindValue result indent second.nextId
        (← CallGraphRenderer.binaryValue operation first.value second.value)
      return ⟨first.lines ++ second.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .ternary operation first second third => do
      unless target == .word do throw (.unsupportedExpression "non-Word ternary result")
      let first := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent nextId first))
      let second := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent first.nextId second))
      let third := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent second.nextId third))
      let bound := CallGraphRenderer.bindValue .word indent third.nextId
        (CallGraphRenderer.ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .apply (.var index) argument => do
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let argument ← render functions .word bindings indent nextId argument
      let value ← requireValue argument
      let result := bindValue .word indent argument.nextId (callee ++ "(" ++ value ++ ")")
      return ⟨argument.lines ++ result.lines, result.value, result.nextId⟩
  | .integer _ => .error (.unsupportedExpression "integer")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .newCell _ _ => .error (.unsupportedExpression "newCell outside direct Word let initializer")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

/-- The raw opcode aliases of `Primitive.opcodeImport`, in the same order. -/
def opcodeAliases : List String :=
  ["div as sc_div", "mod as sc_mod", "shl as sc_shl", "shr as sc_shr", "sar as sc_sar",
    "sdiv as sc_sdiv", "smod as sc_smod", "sgt as sc_sgt", "addmod as sc_addmod", "mulmod as sc_mulmod",
    "clz as sc_clz", "byte as sc_byte", "exp as sc_exp", "signextend as sc_signextend"]

/-- Whether rendering prints a raw alias: Clz, a binary operation outside the
original scalar set, or any ternary operation. Expressions this renderer
rejects, such as data constructors, never reach an import decision. -/
def usesOpcodeAliases : Expr → Bool
  | .unary operation operand => operation == .wordClz || usesOpcodeAliases operand
  | .binary operation left right =>
      (CallGraphRenderer.supportedBinary operation && !Source.supportedBinary operation) ||
        usesOpcodeAliases left || usesOpcodeAliases right
  | .ternary _ _ _ _ => true
  | .letE first second | .pair first second | .apply first second | .storeCell first second =>
      usesOpcodeAliases first || usesOpcodeAliases second
  | .ifE first second third | .caseE first second third =>
      usesOpcodeAliases first || usesOpcodeAliases second || usesOpcodeAliases third
  | .first operand | .second operand | .inLeft _ operand | .inRight _ operand
  | .newCell _ operand | .loadCell operand | .lambda _ _ operand => usesOpcodeAliases operand
  | .unit | .bool _ | .word _ | .integer _ | .var _ | .construct _ _ | .matchData _ _ _ _ => false

/-- Emitters without another `std.opcodes` import add the alias import only
when a rendered body uses an alias; other programs keep their exact text. -/
def opcodeImports (bodies : List Expr) : List String :=
  if bodies.any usesOpcodeAliases then
    ["import { " ++ ", ".intercalate opcodeAliases ++ " } from std.opcodes;"]
  else []

/-- Emitters with an existing `std.opcodes` import append the aliases to it,
again only when a rendered body uses one. -/
def opcodeImportWith (names : List String) (bodies : List Expr) : String :=
  "import {" ++ ", ".intercalate (names ++ if bodies.any usesOpcodeAliases then opcodeAliases else []) ++
    "} from std.opcodes;"

end Solcore.Synthesis.Source.AggregateRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateEmitter
/-! Source pairs and sums remain internal to Word helper functions. The
original checked Core DAG supplies an independent runtime oracle.
`ScalarMeaning.Aggregate.emit_source_meaning` relates the emitted text to the
original Core result under an independent source semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Aggregate

open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

def emitterVersion : String := "solcore-source-aggregates-v2"
def wrapperVersion : String := "solcore-word-aggregates-contract-v1"

/-- The G0 features `emit` renders in helpers: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedAggregates"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAggregatesDeploy"]
def runtimePath : List String := ["SynthesizedAggregatesDeploy", "SynthesizedAggregates"]

def emit (graph : CheckedDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (graph.helpers ++ [graph.entry]) ++ [""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_input"] 8 0 graph.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ result ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Aggregate
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateCases
/-! Replayable aggregate cases retain structural pairs, sums, payload scopes and
private Word cells in the independent Core oracle. The older profiles and their
replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Aggregate
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-aggregate-case.v1"
def profileVersion : String := "runtime-aggregates-v2/template-seed-v1"
def templateVersion : String := "word-aggregate-templates-v1"

structure CheckedInput where
  function : Aggregates.CheckedDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : Aggregates.CheckedDAG) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : Aggregates.CheckedDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Aggregates.version),
    ("templateVersion", toJson templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : Aggregates.CheckedDAG) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied function DAG exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String Aggregates.CheckedDAG := do
  let some function := Aggregates.CheckedDAG.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word function DAG"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic function case schema"
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [], body := .apply functionBody (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := Aggregates.CheckedDAG.ofProgram? {
        resultType := .function .word .word, dataDefinitions := [], body := functionBody } |
        throw "applied function is outside the checked function DAG profile"
      return ⟨function, input⟩
  | _ => throw "function case program is not a closed Word function DAG application"

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def load (index : Nat) : Wire.Expr := .loadCell (.var index)

/-- Both tags are reached by the four boundary inputs. The payloads are
already-evaluated Word expressions; the surrounding renderer must preserve
that order when creating the aggregate. -/
private def chooseSum (input left right : Wire.Expr) : Wire.Expr :=
  .ifE (.binary .wordGt input (word (2 ^ 255 - 1)))
    (.inRight .word right) (.inLeft .word left)

/-- A closed G0 subtree remains closed under all local and payload binders.
The templates combine aggregates with the same private Word-cell discipline as
the mutation profile. Their result is always a Word. -/
def template (pattern : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  .letE scalar (.letE (.newCell .word (.var 1)) (
    if pattern = 0 then
      -- Pair construction snapshots its left load before the right store.
      .letE (.pair (load 0) (.letE (.storeCell (.var 0) (.var 1)) (load 1)))
        (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))
    else if pattern = 1 then
      .letE (chooseSum (.var 2) (load 0) (load 0))
        (.caseE (.var 0)
          (.letE (.storeCell (.var 2) (.binary .wordAdd (.var 0) (.var 3))) (load 3))
          (.letE (.storeCell (.var 2) (.binary .wordXor (.var 0) (.var 3))) (load 3)))
    else if pattern = 2 then
      -- Case results use product and sum joins before a final Word projection.
      .letE (.pair (load 0) (.var 1))
        (.letE (chooseSum (.first (.var 0)) (.first (.var 0)) (.second (.var 0)))
          (.letE (.caseE (.var 0)
            (.pair (.var 0) (.letE (.storeCell (.var 3) (.var 4)) (load 4)))
            (.pair (.first (.var 2)) (.binary .wordAdd (.var 0) (.var 4))))
            (.letE (.caseE (.var 1)
              (.inLeft .word (.binary .wordAdd (.first (.var 1)) (.second (.var 1))))
              (.inRight .word (.binary .wordAdd (.first (.var 1)) (.second (.var 1)))))
              (.caseE (.var 0) (.var 0) (.var 0)))))
    else
      -- Nested cases add two payload binders; the saved Word and Unit bindings
      -- remain in the cell index even when source Unit values need no name.
      let inner := .letE (.var 0)
        (.letE (.storeCell (.var 4) (.binary .wordAdd (.var 0) (.var 2))) (load 5))
      .letE (chooseSum (.var 2) (load 0) (load 0))
        (.caseE (.var 0)
          (.caseE (.inLeft .word (.binary .wordAdd (.var 0) (.var 3))) inner inner)
          (.caseE (.inRight .word (.binary .wordXor (.var 0) (.var 3))) inner inner))))

private def helperBody (index pattern : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  let body := template pattern scalar
  if index = 0 then body else .apply (.var 1) body

private def patternFor (seed : Seed) : Nat := seed.toNat / 3 % 4

private def appliedNodes (helpers : List Wire.Expr) : Nat := Wire.programNodes {
  resultType := .word, dataDefinitions := [],
  body := .apply (functionDAGExpression helpers (.apply (.var 1) (.var 0))) (word 0) }

/-- Budget from the actual full applied skeleton, with one scalar placeholder
per helper. The final measured program is checked again after generation. A
caller generating several steps for one case supplies that case's mask. -/
def generatedFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (mask? : Option FeatureMask := none) : Except String (Aggregates.CheckedDAG × Json) := do
  let count := 1 + seed.toNat % 3
  let skeleton := (List.range count).map fun index =>
    let helperSeed := Seed.ofNat (seed.toNat + index)
    helperBody index (patternFor helperSeed) (word 0)
  let skeletonNodes := appliedNodes skeleton
  unless nodes ≤ 512 && skeletonNodes ≤ nodes do
    throw "node budget is too small for the selected aggregate template or exceeds 512"
  let scalarBudget := (nodes - (skeletonNodes - count)) / count + 2
  let mut helpers : List Wire.Expr := []
  let mut metadata : Array Json := #[]
  let mut finalSeed := seed
  -- One mask for every helper of the case.
  let mask := mask?.getD (revision.caseMask seed featureSupport)
  for index in List.range count do
    let helperSeed := Seed.ofNat (seed.toNat + index)
    let generated ←
      (generate {seed := helperSeed, maxProgramNodes := scalarBudget, revision, mask}).mapError reprStr
    let pattern := patternFor helperSeed
    let body := helperBody index pattern generated.program.body
    helpers := helpers ++ [body]
    metadata := metadata.push (Json.mkObj [
      ("index", toJson index), ("seed", toJson (toString helperSeed.toNat)),
      ("finalSeed", toJson (toString generated.finalSeed.toNat)),
      ("maxProgramNodes", toJson scalarBudget), ("template", toJson pattern)])
    finalSeed := generated.finalSeed
  let some function := Aggregates.CheckedDAG.ofParts? helpers (.apply (.var 1) (.var 0)) |
    throw "generated helper chain did not pass the full Core checker"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied helper chain exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "aggregate-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", toJson (toString finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
    ("helperCount", toJson count), ("helpers", .arr metadata)]
  return (function, origin)

def boundaryResults (function : Aggregates.CheckedDAG) (fuel : Nat) : Except String (List Word) :=
  Input.boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : Aggregates.CheckedDAG) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"
  acceptance.check Input.boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (function, origin) ← generatedFunction seed nodes revision
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "aggregate-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Input.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Aggregates.version), ("templateVersion", templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function DAG"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the function wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core function DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "aggregate-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported function case origin"
  if kind = "aggregate-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "helperCount", "helpers"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated helper provenance")
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function DAG differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Input.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel (← Acceptance.ofOrigin origin)
  return makeCase admitted.function admitted.input emitted origin fuel revision mask

/-- Case payload markers are distinct from ordinary Word let binders. This
prevents a reduction from silently trading a payload scope for a local binder. -/
inductive Binding where
  | local (kind : Aggregates.Local)
  | leftPayload
  | rightPayload
  deriving DecidableEq, BEq, Repr

/-- Binder kinds in expression preorder, including both case payload scopes. -/
def bindingKinds (locals : List Aggregates.Local) (prior : Nat) : Wire.Expr → List Binding
  | .letE initializer body =>
      match Aggregates.initializerKind? locals prior initializer with
      | none => []
      | some kind => bindingKinds locals prior initializer ++ [.local kind] ++
          bindingKinds (kind :: locals) prior body
  | .caseE scrutinee left right =>
      bindingKinds locals prior scrutinee ++ [.leftPayload] ++
        bindingKinds (.word :: locals) prior left ++ [.rightPayload] ++
        bindingKinds (.word :: locals) prior right
  | .ifE condition yes no | .ternary _ condition yes no =>
      bindingKinds locals prior condition ++ bindingKinds locals prior yes ++ bindingKinds locals prior no
  | .binary _ left right | .pair left right =>
      bindingKinds locals prior left ++ bindingKinds locals prior right
  | .unary _ operand | .newCell _ operand | .first operand | .second operand |
      .inLeft _ operand | .inRight _ operand => bindingKinds locals prior operand
  | .apply _ argument | .storeCell _ argument => bindingKinds locals prior argument
  | _ => []

def bindingInventory (function : Aggregates.CheckedDAG) : List Binding :=
  (function.helpers.zipIdx.flatMap fun (body, index) => bindingKinds [.word] index body) ++
    bindingKinds [.word] function.helpers.length function.entry

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  sameBindings : bindingInventory candidate.function = bindingInventory source.function
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (helpers : List Wire.Expr)
    (entry : Wire.Expr) (input : Word) : Option (Reduction source) := do
  let function ← Aggregates.CheckedDAG.ofParts? helpers entry
  let candidate : CheckedInput := ⟨function, input⟩
  if count : candidate.function.helpers.length = source.function.helpers.length then
    if bindings : bindingInventory candidate.function = bindingInventory source.function then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
        then some ⟨candidate, count, bindings, strict⟩ else none
    else none
  else none

/-- Rewrites retain every typed let and both case payload scopes. A case
branch is never extracted. Whole-DAG checking and the distinct binder inventory
are checked again before exposing a strictly smaller candidate. -/
private def bodyReductions (locals : List Aggregates.Local) (prior : Nat)
    (expression : Wire.Expr) : List Wire.Expr :=
  let canonical := if (bindingKinds locals prior expression).isEmpty then
      match Aggregates.initializerKind? locals prior expression with
      | some .word => [word 0]
      | some .bool => [.bool false]
      | some .unit => [.unit]
      | some .wordPair => [.pair (word 0) (word 0)]
      | some .wordSum => [.inLeft .word (word 0)]
      | _ => []
    else []
  canonical ++ match expression with
  | .letE initializer body =>
      match Aggregates.initializerKind? locals prior initializer with
      | none => []
      | some kind =>
          ((bodyReductions locals prior initializer).filter fun changed =>
            Aggregates.initializerKind? locals prior changed == some kind).map
              (fun changed => .letE changed body) ++
          (bodyReductions (kind :: locals) prior body).map (.letE initializer)
  | .ifE condition yes no =>
      (bodyReductions locals prior condition).map (fun changed => .ifE changed yes no) ++
      (bodyReductions locals prior yes).map (fun changed => .ifE condition changed no) ++
      (bodyReductions locals prior no).map (.ifE condition yes)
  | .unary operation operand =>
      (bodyReductions locals prior operand).map (.unary operation)
  | .binary operation left right =>
      (bodyReductions locals prior left).map (fun changed => .binary operation changed right) ++
      (bodyReductions locals prior right).map (.binary operation left)
  | .ternary operation first second third =>
      (bodyReductions locals prior first).map (fun changed => .ternary operation changed second third) ++
      (bodyReductions locals prior second).map (fun changed => .ternary operation first changed third) ++
      (bodyReductions locals prior third).map (.ternary operation first second)
  | .pair left right =>
      (bodyReductions locals prior left).map (fun changed => .pair changed right) ++
      (bodyReductions locals prior right).map (.pair left)
  | .first operand => (bodyReductions locals prior operand).map .first
  | .second operand => (bodyReductions locals prior operand).map .second
  | .inLeft type payload => (bodyReductions locals prior payload).map (.inLeft type)
  | .inRight type payload => (bodyReductions locals prior payload).map (.inRight type)
  | .caseE scrutinee left right =>
      (bodyReductions locals prior scrutinee).map (fun changed => .caseE changed left right) ++
      (bodyReductions (.word :: locals) prior left).map (fun changed => .caseE scrutinee changed right) ++
      (bodyReductions (.word :: locals) prior right).map (.caseE scrutinee left)
  | .newCell .word initializer =>
      (bodyReductions locals prior initializer).map (.newCell .word)
  | .storeCell reference value =>
      (bodyReductions locals prior value).map (.storeCell reference)
  | .apply function argument =>
      (bodyReductions locals prior argument).map (.apply function)
  | _ => []

def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (List Wire.Expr × Wire.Expr × Word) := []
  for (body, index) in source.function.helpers.zipIdx do
    for changed in bodyReductions [.word] index body do
      raw := raw ++ [(source.function.helpers.set index changed, source.function.entry, source.input)]
  for changed in bodyReductions [.word] source.function.helpers.length source.function.entry do
    raw := raw ++ [(source.function.helpers, changed, source.input)]
  for input in [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)] do
    raw := raw ++ [(source.function.helpers, source.function.entry, input)]
  let mut seen : List String := []
  let mut result := []
  for (helpers, entry, input) in raw do
    if let some reduced := sealReduction source helpers entry input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Aggregate
end

section
-- leanmerge: from Solcore.Synthesis.Source.AggregateCallGraphCases
/-! Replayable cases for directly generated graphs that compose Word pairs,
Word sums, projections and case payload scopes with helper calls. The original
Core lambda chain is retained and executed independently of source lowering.
The template aggregate and scalar call-graph profiles remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateCallGraph
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-aggregate-call-graph-case.v1"
def profileVersion : String := "runtime-aggregate-call-graphs-v1/direct-grammar-v1"
def functionVersion : String := Aggregates.version
def generatorVersion : String := Solcore.Synthesis.Core.AggregateCallGraph.version
def boundaryVersion : String := Primitive.boundaryVersion
def shapeVersion : String := Solcore.Synthesis.Core.AggregateCallGraph.shapeVersion
def boundaryInputs : List Word := Primitive.boundaryInputs
def minimumProgramNodes : Nat := Solcore.Synthesis.Core.AggregateCallGraph.minimumAppliedNodes 1

def aggregateShapes (function : Aggregates.CheckedDAG) : List String :=
  Solcore.Synthesis.Core.AggregateCallGraph.structuralShapes function

def inputWord := Primitive.inputWord

structure CheckedInput where
  function : Aggregates.CheckedDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : Aggregates.CheckedDAG) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : Aggregates.CheckedDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson functionVersion), ("boundaryVersion", toJson boundaryVersion),
    ("shapeVersion", toJson shapeVersion), ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features), ("helperCount", toJson function.helpers.length),
    ("aggregateShapes", toJson (aggregateShapes function))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : Aggregates.CheckedDAG) (input : Word)
    (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Solcore.Synthesis.Core.AggregateCallGraph.graphWithinGrammar function do
    throw "aggregate graph is outside the call-graph composition grammar"
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied aggregate graph exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

private def admitted (program : Wire.Program) : Except String Aggregates.CheckedDAG := do
  let some function := Aggregates.CheckedDAG.ofProgram? program |
    throw "program is not a checked aggregate Word function DAG"
  unless Solcore.Synthesis.Core.AggregateCallGraph.graphWithinGrammar function do
    throw "aggregate graph is outside the call-graph composition grammar"
  return function

def checkedFunction (json : Json) : Except String Aggregates.CheckedDAG := do
  admitted (← decodeProgram json)

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic aggregate call-graph case schema"
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [], body := .apply functionBody (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let function ← admitted {resultType := .function .word .word, dataDefinitions := [], body := functionBody}
      let value : CheckedInput := ⟨function, input⟩
      unless Wire.encodeProgram value.program == (← json.getObjVal? "program") do
        throw "saved Core aggregate graph application is not canonical"
      return value
  | _ => throw "aggregate call-graph case program is not a closed Word function DAG application"

def generatedFunction (seed : Seed) (nodes : Nat) :
    Except String (Aggregates.CheckedDAG × Json) := do
  let generated ← (Solcore.Synthesis.Core.AggregateCallGraph.generate
    {seed, maxProgramNodes := nodes}).mapError reprStr
  let origin := Json.mkObj [
    ("kind", toJson "aggregate-call-graph-generated"),
    ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes),
    ("helperCount", toJson generated.function.helpers.length),
    ("bodyBudgets", toJson generated.bodyBudgets)]
  return (generated.function, origin)

/-- Helper-only calls are dead without an entry call. This is a syntactic
condition, not a claim that a branch, call or payload executes. -/
def hasEntryCall (function : Aggregates.CheckedDAG) : Bool :=
  (Aggregates.features function.entry).contains "functionCall"

def hasCallComposition (function : Aggregates.CheckedDAG) : Bool :=
  (aggregateShapes function).any Solcore.Synthesis.Core.AggregateCallGraph.callCompositionShapes.contains

def boundaryResults (function : Aggregates.CheckedDAG) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- Generated graphs need an entry call, a syntactic composition of a call with
an aggregate value or payload scope, and varied results over the eight inputs. -/
def inputSensitive (function : Aggregates.CheckedDAG) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  unless hasEntryCall function do throw "entry has no helper call"
  unless hasCallComposition function do throw "no call composes with an aggregate value or payload"
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check boundaryInputs results

/-- Attempts count complete graph candidates. Accepted graphs yield up to eight
cases in fixed input order. Fuel exhaustion is an inconclusive exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (function, origin) ← generatedFunction seed nodes
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "aggregate-call-graph-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  let admitted ← caseProgram json
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds profile limit"
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", functionVersion), ("boundaryVersion", boundaryVersion),
      ("shapeVersion", shapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core aggregate graph"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the aggregate call-graph wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core aggregate graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.function.helpers.length do
    throw "saved helper count differs from the original Core aggregate graph"
  unless (← provenance.getObjVal? "aggregateShapes") == toJson (aggregateShapes admitted.function) do
    throw "saved aggregate shapes differ from the original Core aggregate graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "aggregate-call-graph-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved aggregate graph differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive function validationFuel acceptance
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "generated aggregate graph provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported aggregate graph provenance is not canonical"
  else if kind = "reduced" then
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [
      ("schema", toJson caseSchema), ("program", parentProgram), ("input", toJson parentText)])
    unless admitted.function.helpers.length = parent.function.helpers.length do
      throw "saved graph reduction changes helper count"
    unless Aggregate.bindingInventory admitted.function = Aggregate.bindingInventory parent.function do
      throw "saved graph reduction changes typed binders or payload scopes"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved graph reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentInput", toJson parentText)] do
      throw "reduced aggregate graph provenance is not canonical"
  else throw "unsupported aggregate call-graph case origin"
  let fresh := makeCase admitted.function admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "aggregate call-graph provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved aggregate call-graph case envelope is not canonical"
  return fresh

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.function = Aggregate.bindingInventory source.function
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- Reuse the typed aggregate reductions: every typed let, both case payload
scopes and every helper binding are retained, and each result was resealed.
Their canonical replacements stay inside this profile's grammar. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (Aggregate.reductions ⟨source.function, source.input⟩).map fun reduced =>
    ⟨⟨reduced.candidate.function, reduced.candidate.input⟩, reduced.sameHelperCount,
      reduced.sameBindings, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.function reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.AggregateCallGraph
end
