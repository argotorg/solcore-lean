import Solcore.Syntax.Parser.Term
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Original source rejection remains distinct from selected raw success.
Owner covariance preserves scope guards; it is not arbitrary-child correctness. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationOwnerBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OwnerBoundary",by decide⟩],by decide⟩⟩,128⟩
private def lid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 900},999999⟩
private def mapping (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective mapping := by rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [mapping] using same
private def relabel := ownerLocalIdMap mapping
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective mapping injective
private def inputs : LocalTypeInputs := ⟨[⟨"x",lid 7,.word⟩,⟨"c",foreign,.bool⟩,⟨"x",lid 2,.bool⟩],by decide⟩
private def renamed := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool)]
private def word := Core.Value.word (Core.Word.ofNatModulo 14)
private def env (c : Bool) : Resolved.Environment := [(lid 7,word),(foreign,.bool c),(lid 2,.bool false)]
private def core : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-owner-boundary.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parser")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span=⟨file.id,0,text.utf8ByteSize⟩)) "original full block bytes"
  return body
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context s)) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : i.names.lookup? name.value with
    | some localId => match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | _ => throw (IO.userError "static name")
  | _ => throw (IO.userError "static child")
private def body (i : LocalTypeInputs) (s : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i s)) := do
  check (s.value.all fun st => s.span.contains st.span) "original statement ranges"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ => let c ← child i expression; return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let b ← body i ⟨span,statements⟩; return ⟨b.core,b.type,by rw [shape]; exact .block b.evidence⟩
  | ⟨span,⟨ls,.letDecl name none (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte≤init.span.startByte)) "original inferred initializer before binding"
      let c ← child i init; let b ← body (i.bindFresh owner name.value c.type) ⟨span,rest⟩
      return ⟨.letE c.core b.core,b.type,by rw [shape]; exact .inferred c.evidence b.evidence⟩
  | ⟨_,[⟨span,.ifThen condition yes (some no)⟩]⟩ =>
      check (span.contains condition.span && span.contains yes.span && span.contains no.span && decide (condition.span.endByte≤yes.span.startByte ∧ yes.span.endByte≤no.span.startByte)) "original branch order"
      let c ← child i condition; let a ← body i yes; let b ← body i no
      if same : c.type=.bool ∧ b.type=a.type then
        if guard : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then
          return ⟨.ifE c.core a.core b.core,a.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) (computationBlockPreservesNames_iff.mp guard) a.evidence (same.2 ▸ b.evidence)⟩
        else throw (IO.userError "exposed original name")
      else throw (IO.userError "branch types")
  | _ => throw (IO.userError "static body")
termination_by sizeOf s
private structure Atom (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table e store s value store 1
private def atom (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (Atom table e s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some localId => match found : e.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _ => throw (IO.userError "raw row")
    | _ => throw (IO.userError "raw name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table e store s value store cost
private def raw (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Block) : IO (Raw table e s) := do
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ => let c ← atom table e expression; return ⟨c.value,1,fun st => by rw [shape]; exact .expression (c.evidence st)⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let b ← raw table e ⟨span,statements⟩; return ⟨b.value,b.cost,fun st => by rw [shape]; exact .block (b.evidence st)⟩
  | ⟨span,⟨_,.letDecl name ann (some init)⟩::rest⟩ =>
      let c ← atom table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let b ← raw ((name.value,fresh)::table) ((fresh,c.value)::e) ⟨span,rest⟩
      return ⟨b.value,1+b.cost+2,fun st => by
        rw [shape]; cases ann with
        | none => exact .inferred (c.evidence st) (b.evidence st)
        | some _ => exact .binding (c.evidence st) (b.evidence st)⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← atom table e condition
      match selected : c.value with
      | .bool true => let b ← raw table e yes; return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifTrue (selected ▸ c.evidence st) (b.evidence st)⟩
      | .bool false => let b ← raw table e no; return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifFalse (selected ▸ c.evidence st) (b.evidence st)⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf s
private theorem path (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 7 else 4) ⟨.eval core (env c).values,k,store⟩ ⟨.ret word,k,store⟩ := by
  cases c
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
private def positive : IO Unit := do
  let s ← parsed "{if(c){{let x=x;return x;}}else{return x;}}"
  let p ← body inputs s
  if fixed : p.core=core ∧ p.type=.word then
    have original : RecursiveComputationReturnTreeElaborates types owner inputs s core .word := by simpa only [fixed.1,fixed.2] using p.evidence
    have preserved := (computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mpr original
    have _ := (computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mp preserved
    have typed := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩
    have _ := (computationReturnTreeHasType_mapOwner_iff mapping injective (recursiveLocalComputationHasType_mapIds_iff _ relabel_injective)).mpr typed
    have accepted := (elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner inputs s).trans
      ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original)
    for c in [false,true] do
      let r ← raw inputs.names (env c) s; let cost := if c then 7 else 4
      if independent : r.value=word ∧ r.cost=cost then
        for store in [[],[Core.Value.bool true,.cellRef .word 700]] do
          have _ : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env c) store s word store cost := by simpa only [independent.1,independent.2] using r.evidence store
          for fuel in List.range (cost+2) do
            have _ := (path c store []).runStateful_done_iff (fuel := fuel)
            have _ := accepted
            check (decide ((elaborateRecursiveComputationReturnTree? types (mapping owner) renamed s).map
              (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel (env c)).values store)))=
              some (.word,Core.runStateful fuel (.initial core (env c).values store)))) "original exact Core and complete mapped run"
            match genuine : Core.runStateful fuel (.initial core (env c).values store) with
            | .done v st => check (decide (cost≤fuel ∧ v=word ∧ st=store)) "independent original completion"
            | .outOfFuel cp =>
                have _ := (path c store []).residual_of_outOfFuel genuine
                for more in [0,1,cost-fuel] do
                  check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel (env c)).values store))) "genuine checkpoint full resumption"
            | .fault _ _ => throw (IO.userError "unexpected static fixture fault")
      else throw (IO.userError "independent raw cost/value")
  else throw (IO.userError "independent original static Core/type")
private def rejected (text : String) (yesCost noCost : Nat) (yesValue noValue : Core.Value) : IO Unit := do
  let s ← parsed text
  if absence : elaborateRecursiveComputationReturnTree? types owner inputs s=none then
    have equality := elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner inputs s
    have noOriginal : ¬ ∃ ce ty, RecursiveComputationReturnTreeElaborates types owner inputs s ce ty := by
      rintro ⟨ce,ty,h⟩; have impossible := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr h
      change elaborateRecursiveComputationReturnTree? types owner inputs s=some (ce,ty) at impossible
      rw [absence] at impossible; cases impossible
    have noMapped : ¬ ∃ ce ty, RecursiveComputationReturnTreeElaborates types (mapping owner) renamed s ce ty := by
      rintro ⟨ce,ty,h⟩; exact noOriginal ⟨ce,ty,(computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mp h⟩
    have _ := noMapped
    check (decide (elaborateRecursiveComputationReturnTree? types (mapping owner) renamed s=none)) "whole rejection retained"
    have _ := equality
    for c in [false,true] do
      let r ← raw inputs.names (env c) s
      if independent : r.cost=(if c then yesCost else noCost) ∧ r.value=(if c then yesValue else noValue) then
        have _ : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env c) store s (if c then yesValue else noValue) store (if c then yesCost else noCost) := by simpa only [independent.1,independent.2] using r.evidence
        pure ()
      else throw (IO.userError "selected raw path must remain separate")
  else throw (IO.userError "whole source unexpectedly accepted")
private def identitySensitive (table : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if table.lookup? "x"=some (lid 7) then some (.var 99,.word) else none
private def arbitraryCheckerBoundary : IO Unit := do
  let s ← parsed "{return x;}"
  check (decide (elaborateComputationReturnTree? identitySensitive types owner inputs s=some (.var 99,.word) ∧
    elaborateComputationReturnTree? identitySensitive types (mapping owner) renamed s=none)) "injective owner map alone does not imply arbitrary checker covariance"
  let constant := fun (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) => some (Core.Expr.var 99,Core.Ty.word)
  have _ := elaborateComputationReturnTree?_mapOwner mapping injective constant (fun _ _ _ => rfl) types owner inputs s
  for fuel in [0,1,2] do
    let initial := Core.State.initial (.var 99) (env true).values []
    let expected := Core.StatefulRunResult.fault (.unboundVariable 99) initial
    check (decide (Core.runStateful fuel initial=expected)) "literal arbitrary-child failure threshold"
    check (decide ((elaborateComputationReturnTree? constant types (mapping owner) renamed s).map
      (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel (env true)).values [])))=
      some (.word,Core.runStateful fuel (.initial (.var 99) (env true).values [])))) "covariant arbitrary checker may preserve failure"
end ParsedComputationOwnerBoundaries
open ParsedComputationOwnerBoundaries in
def frontendParsedComputationOwnerBoundaryTests : IO Unit := do
  check (decide ((inputs.bindFresh owner "x" .word).ids=[lid 8,lid 7,foreign,lid 2] ∧
    (renamed.bindFresh (mapping owner) "x" .word).ids=[relabel (lid 8),relabel (lid 7),relabel foreign,relabel (lid 2)])) "foreign high index never drives local fresh allocation"
  positive
  rejected "{if(c){let x=x;return x;}else{return x;}}" 7 4 word word
  rejected "{if(c){return x;}else{let y:Missing=x;return y;}}" 4 7 word word
  rejected "{if(c){return c;}else{return x;}}" 4 4 (.bool true) word
  arbitraryCheckerBoundary
end Tests
