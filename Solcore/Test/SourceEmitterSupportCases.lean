import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.NestedLoopCases
import Solcore.Synthesis.Source.RecursionCases
import Solcore.Synthesis.Source.RecursiveLoopCases
import Solcore.Synthesis.Source.LoopClosureCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.AssemblyCases
import Solcore.Synthesis.Source.AssemblyMemoryCases

/-! The G0 features each pure profile declares are exactly those its emitter
renders: a probe program for each catalog feature emits if and only if the
feature is declared. Revision four restricts swarm masks to these sets. -/
set_option autoImplicit false

namespace Tests.SourceEmitterSupportCases

open Solcore.Core.Wire
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Expr := .word (Solcore.Core.Word.ofNatModulo value)

private def comparison : BinaryOp → Bool
  | .wordEq | .wordGt | .wordSgt => true
  | _ => false

/-- A Word expression over `argument` whose only operator or form is `feature`,
except that a Bool-valued feature selects between two Words with `if`. -/
private def probe (argument : Expr) : Feature → Expr
  | .unary .boolNot => .ifE (.unary .boolNot (.bool true)) argument (word 1)
  | .unary operation => .unary operation argument
  | .binary operation =>
      if comparison operation then .ifE (.binary operation argument (word 3)) argument (word 1)
      else .binary operation argument (word 3)
  | .ternary operation => .ternary operation argument (word 2) (word 3)
  | .letE => .letE argument (.var 0)
  | .ifE => .ifE (.bool true) argument (word 1)
  | _ => argument

private def emits {ε α : Type} (result : Except ε α) : Bool := result matches .ok _

private def closed (body : Expr) : Option CheckedWordProgram :=
  CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body}

/-- The entry of a one-helper graph applies the helper to the input. -/
private def entry : Expr := .apply (.var 1) (.var 0)

private def step (helper : Expr) : Option Aggregates.CheckedDAG := Aggregates.CheckedDAG.ofParts? [helper] entry

private def fixedConstant : Option CheckedWordProgram := closed (.binary .wordAdd (word 1) (word 2))

private def fixedStep : Option Aggregates.CheckedDAG := step (.binary .wordAdd (.var 0) (word 1))

/-- Two stages, one with each width, an unaligned final read and a 33-byte hash. -/
private def memorySchedule : AssemblyMemory.Schedule :=
  {stages := [⟨7, .word, 13⟩, ⟨40, .byte, 70⟩], final := 33, hash := some ⟨5, 33⟩}

private structure Profile where
  name : String
  support : FeatureMask
  /-- Whether the emitter renders the probe of a feature; none when the probe
  itself fails the profile's checker. -/
  emits : Feature → Option Bool

private def profiles : List Profile := [
  ⟨"closed-g0", featureSupport, fun feature =>
    (closed (probe (word 5) feature)).map (emits ∘ emit)⟩,
  ⟨"runtime-word", Input.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Input.emit)⟩,
  ⟨"runtime-primitives", Primitive.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Primitive.emit)⟩,
  ⟨"runtime-assembly switch", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .switch)⟩,
  ⟨"runtime-assembly if", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .branches)⟩,
  ⟨"runtime-assembly operations", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .operations)⟩,
  ⟨"runtime-assembly-memory", AssemblyMemory.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map fun function =>
      emits (AssemblyMemory.emit function memorySchedule)⟩,
  ⟨"runtime-functions", Solcore.Synthesis.Source.Function.featureSupport, fun feature =>
    (CheckedWordFunctionDAG.ofParts? [probe (.var 0) feature] entry).map
      (emits ∘ Solcore.Synthesis.Source.Function.emit)⟩,
  ⟨"runtime-mutation", Mutation.featureSupport, fun feature =>
    (LocalMutation.CheckedDAG.ofParts? [probe (.var 0) feature] entry).map (emits ∘ Mutation.emit)⟩,
  ⟨"runtime-aggregates", Aggregate.featureSupport, fun feature =>
    (step (probe (.var 0) feature)).map (emits ∘ Aggregate.emit)⟩,
  ⟨"runtime-loops", Loop.featureSupport, fun feature => do
    let plan ← BoundedLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3
    return emits (Loop.emit plan)⟩,
  ⟨"runtime-nested-loops", NestedLoop.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.NestedLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3 3
      .accumulator
    return emits (NestedLoop.emit plan)⟩,
  ⟨"runtime-recursion", Recursion.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Recursion.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 7 .mutual
    return emits (Recursion.emit plan)⟩,
  ⟨"runtime-recursive-loops", RecursiveLoop.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.RecursiveLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3 3 .mutual
    return emits (RecursiveLoop.emit plan)⟩,
  ⟨"runtime-loop-closures", LoopClosure.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.LoopClosure.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 7 .counter
    return emits (LoopClosure.emit plan)⟩,
  ⟨"runtime-generics", Generic.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Generic.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) .word
    return emits (Generic.emit plan)⟩,
  ⟨"runtime-closures", Closure.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Closure.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) .snapshot
    return emits (Closure.emit plan)⟩,
  ⟨"runtime-comptime step", Comptime.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Comptime.CheckedPlan.ofParts? (← fixedConstant)
      (← step (probe (.var 0) feature)) .offset
    return emits (Comptime.emit plan)⟩,
  ⟨"runtime-comptime constant", Comptime.constantSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Comptime.CheckedPlan.ofParts? (← closed (probe (word 5) feature))
      (← fixedStep) .offset
    return emits (Comptime.emit plan)⟩,
  ⟨"runtime-modules step", Modules.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Modules.CheckedPlan.ofParts? (← fixedConstant)
      (← step (probe (.var 0) feature))
    return emits (Modules.emit plan)⟩,
  ⟨"runtime-modules constant", Modules.constantSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Modules.CheckedPlan.ofParts? (← closed (probe (word 5) feature))
      (← fixedStep)
    return emits (Modules.emit plan)⟩]

private def indices (mask : FeatureMask) : List Nat :=
  (FeatureMask.catalog.zipIdx.filter fun (feature, _) => mask.allows feature).map (·.2)

def testSourceEmitterSupportCases : IO Unit := do
  ensure (indices scalarSupport == [0, 1, 3, 4, 5, 8, 9, 10, 19, 20, 24, 25] &&
      PrimitiveRenderer.support == FeatureMask.all && AssemblyRenderer.support == FeatureMask.all &&
      AggregateRenderer.support == FeatureMask.all &&
      MutationRenderer.support == scalarSupport)
    "a renderer's declared G0 features changed"
  for profile in profiles do
    for feature in FeatureMask.catalog do
      let some emitted := profile.emits feature |
        throw (IO.userError s!"{profile.name}: the probe of {featureName feature} failed its checker")
      ensure (emitted == profile.support.allows feature)
        s!"{profile.name}: {featureName feature} emits {emitted} against its declared support"

end Tests.SourceEmitterSupportCases
