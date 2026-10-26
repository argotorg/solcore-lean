import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked event-log protocol around a closed aggregate step. The ABI
supplies a flags Word and an input Word. The contract writes the step result
to slot zero and a counter to slot one, then runs up to three static log sites.
A site whose guard bit is set in the flags applies the step once more and
emits one log with zero to four topics and zero to two data Words.

Core's host interface offers one log primitive, `emitLogWord`, carrying one
topic Word and one payload Word. Each site is therefore written as a frame of
word logs under `framingVersion`: a header naming the topic count and data
length, the data Words, then the topics. The observer decodes committed
journals into multi-topic logs; the frame is a convention of this profile and
not a Core log semantics. The original flags parity then selects return or
revert, and the public contract runtime commits or discards the working world
and journal together. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EventLog

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-event-log-contract-v1"
def framingVersion : String := "core-word-log-framing-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def maxSites : Nat := 3
def maxTopics : Nat := 4
def maxDataWords : Nat := 2

/-- One static log site. `guard` names the flags bit that enables it,
`topics` the log's topic count and `dataWords` its data length in Words. -/
structure Site where
  guard : Nat
  topics : Nat
  dataWords : Nat
  deriving Repr, BEq, DecidableEq

/-- At most three sites, guards one to three in strictly increasing order, at
most four topics and two data Words each. Removing a site keeps the others'
guards, so their emissions do not move to another flags bit. -/
def validSites (sites : List Site) : Bool :=
  sites.length ≤ maxSites &&
    sites.all (fun site => 1 ≤ site.guard && site.guard ≤ 3 &&
      site.topics ≤ maxTopics && site.dataWords ≤ maxDataWords) &&
    (sites.zip (sites.drop 1)).all fun (left, right) => left.guard < right.guard

/-- Frame tags. The header carries payload zero; data and topic records are
numbered from one in emission order. -/
def headerTag (site : Site) : Nat := 256 + 16 * site.dataWords + site.topics
def dataTag (index : Nat) : Nat := 512 + index
def topicTag (index : Nat) : Nat := 768 + index

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- The binder at `position`, counted from the outermost, in a frame with
`depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

private def stepPosition : Nat := 0
private def flagsPosition : Nat := 1
private def inputPosition : Nat := 2
private def oldPosition : Nat := 3
private def countPosition : Nat := 4
private def basePosition : Nat := 5
private def resultPosition : Nat := 6
/-- Binders before the first site: the step, flags, input, both reads, the
base, the result and the two Unit writes. -/
private def siteDepth : Nat := 9

/-- Header, data Words and topics of one site. Each payload is built at the
depth where its record is bound; `value` is the site's own binder. -/
private def frame (site : Site) (value : Nat) : List (Nat × (Nat → Expr)) :=
  [(headerTag site, fun _ => word 0)] ++
    ((List.range site.dataWords).map fun index =>
      (dataTag (index + 1), fun depth => bound depth (if index = 0 then value else resultPosition))) ++
    ((List.range site.topics).map fun index =>
      (topicTag (index + 1), fun depth => .binary .wordAdd (bound depth value) (word (index + 1))))

private def emitRecords (depth : Nat) : List (Nat × (Nat → Expr)) → Expr
  | [] => .unit
  | (tag, payload) :: rest =>
      .letE (host 13 depth (.pair (word tag) (payload depth))) (emitRecords (depth + 1) rest)

/-- A guarded site binds `step(result + guard)` and then its frame records. -/
private def siteExpression (depth : Nat) (site : Site) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound depth flagsPosition) (word (2 ^ site.guard)))
      (word (2 ^ site.guard)))
    (.letE (.apply (bound depth stepPosition)
        (.binary .wordAdd (bound depth resultPosition) (word site.guard)))
      (emitRecords (depth + 1) (frame site depth)))
    .unit

private def completion (depth : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound depth flagsPosition) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (bound depth resultPosition)))
    (.inLeft (.sum .word .word) (bound depth resultPosition))

private def withSites (depth : Nat) : List Site → Expr
  | [] => completion depth
  | site :: rest => .letE (siteExpression depth site) (withSites (depth + 1) rest)

/-- Every host application names its exact local depth. Both writes precede
every log, and every log precedes the completion. -/
private def contractExpression (stepBody : Expr) (sites : List Site) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 1))
            (.letE (.binary .wordAdd (bound 5 inputPosition) (bound 5 oldPosition))
              (.letE (.apply (bound 6 stepPosition) (bound 6 basePosition))
                (.letE (host 1 7 (.pair (word 0) (bound 7 resultPosition)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (bound 8 countPosition) (word 1))))
                    (withSites siteDepth sites)))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (sites : List Site) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body sites
}

/-- Syntax-only overhead measurement; the placeholder is never admitted or run. -/
def programOverhead (sites : List Site) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) sites} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  sites : List Site
  sitesValid : validSites sites = true
  checked : (canonicalProgram step sites).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.sites

def ofParts? (step : Aggregates.CheckedDAG) (sites : List Site) : Option CheckedPlan :=
  if sitesValid : validSites sites = true then
    if checked : (canonicalProgram step sites).check = true then some ⟨step, sites, sitesValid, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.EventLog
