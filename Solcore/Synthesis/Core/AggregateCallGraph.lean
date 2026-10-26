import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.CallGraphGenerator

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
