import Lean

/-!
# DeclSnapshot

Writes one JSON line per constant defined in a set of modules, with hashes that are
invariant under moving declarations between modules (pure-refactor verification).

Usage (from the worktree root):

    lake env lean --run tools/DeclSnapshot.lean <groups.txt> <out.jsonl> [threads]

`groups.txt` lists module names, one per line. A line `---` starts a new import group.
Each group is imported on its own (`importModules`, never freed: run large groups in separate
processes), and every constant whose first
defining module (`Environment.getModuleIdxFor?`) is one of the group's listed modules is
written. Groups exist because the `lean_exe` roots all define `main` and cannot be
imported together. Skipped constants go to `<out.jsonl>.skipped.tsv`.

Normalization:
* private names `_private.<M>.0.n` become `n` with flag `p`;
* macro scopes `_@.<M>...._hyg.<k>` are removed wherever they occur (flag `h`);
* `aux_def` names `_aux_<M>___...` get `<M>` in place of the mangled defining module;
* constants with module-dependent names (private, hygienic, `_aux_`) and module-local
  cached auxiliaries (`_proof_i`, `_simp_i`, `match_i`, `_sparseCasesOn_i`, `_auxLemma`,
  `_arg_pusher`) are referenced *by content* (a hash of kind, type and, except for
  theorems, value) instead of by name, so renaming or reusing them is invisible;
* the cached auxiliaries themselves are not written (their content is covered by the
  constants that use them).
-/

open Lean Meta

namespace DeclSnapshot

@[inline] def mix (a b : UInt64) : UInt64 := mixHash a b

def mixList (seed : UInt64) (xs : List UInt64) : UInt64 := xs.foldl mix seed

def hStr (s : String) : UInt64 := mix 0x5354 (hash s)

def hNat (n : Nat) : UInt64 :=
  if n < 18446744073709551616 then mix 0x4e41 (UInt64.ofNat n) else mix 0x4e42 (hash (toString n))

def hBool (b : Bool) : UInt64 := if b then 0x7472 else 0x6661

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

def allDigits (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- `pre` followed by digits and underscores only, e.g. `_proof_1_6`. -/
def numberedAfter (pre : String) (s : String) : Bool :=
  s.startsWith pre &&
    (let rest := s.toList.drop pre.length
     !rest.isEmpty && rest.all (fun c => c.isDigit || c == '_') && rest.head!.isDigit)

/-- Reason for not writing a constant: module-local cached auxiliaries whose names depend on
which declaration of the module first needed them. -/
def auxComponentReason? (s : String) : Option String :=
  if numberedAfter "_proof_" s then some "aux-lemma(_proof)"
  else if numberedAfter "_simp_" s then some "aux-lemma(_simp)"
  else if numberedAfter "match_" s then some "matcher(match_i)"
  else if numberedAfter "_sparseCasesOn_" s then some "sparse-casesOn"
  else if s == "_auxLemma" || numberedAfter "_auxLemma_" s then some "auxLemma"
  else if s == "_arg_pusher" then some "arg-pusher"
  else if s == "_cstage1" || s == "_cstage2" || numberedAfter "_closed_" s ||
      numberedAfter "_lambda_" s || numberedAfter "_spec_" s || numberedAfter "_elambda_" s ||
      s == "_rarg" || s == "_boxed" || s == "_redArg" then some "compiler-internal"
  else none

def skipReason? (n : Name) : Option String :=
  n.components.findSome? fun c =>
    match c with
    | .str _ s => auxComponentReason? s
    | _ => none

def hasMacroScopeMarker (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s == "_@" || s == "_hyg"
    | _ => false

def hasAuxDefComponent (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s.startsWith "_aux_"
    | _ => false

/-- Names whose spelling depends on the defining module, the file position, or on which
declaration first created a cached auxiliary. References to these are hashed by content. -/
def isUnstable (n : Name) : Bool :=
  isPrivateName n || hasMacroScopeMarker n || hasAuxDefComponent n || (skipReason? n).isSome

/-- Remove macro scopes `_@.<module>...._hyg.<k>...` wherever they occur. -/
def stripMacroScopes (n : Name) : Name := Id.run do
  -- 0 = normal, 1 = inside `_@ ... _hyg`, 2 = after `_hyg` (numeric scopes)
  let mut st : Nat := 0
  let mut out : Name := .anonymous
  for c in n.components do
    match c with
    | .str _ s =>
      if st == 1 then
        if s == "_hyg" then st := 2
      else if s == "_@" then st := 1
      else
        st := 0
        out := .str out s
    | .num _ k =>
      if st == 0 then out := .num out k
    | .anonymous => pure ()
  return out

structure ModCtx where
  mod : Name
  mangled : String
  dotted : String
  deriving Inhabited

def ModCtx.ofModule (m : Name) : ModCtx :=
  { mod := m
    mangled := "_".intercalate (m.components.map fun c => c.toString (escape := false))
    dotted := m.toString (escape := false) }

def replaceAll (s pat repl : String) : String :=
  if pat.isEmpty then s else repl.intercalate (s.splitOn pat)

/-- Normalize module-dependent text inside strings produced by `aux_def` and private names. -/
def normStr (mc : ModCtx) (s : String) : String :=
  if mc.mangled.isEmpty then s
  else
    let s := replaceAll s ("_aux_" ++ mc.mangled ++ "___") "_aux_<M>___"
    let s := replaceAll s ("_private_" ++ mc.mangled ++ "_0_") "_private_<M>_0_"
    replaceAll s ("_private." ++ mc.dotted ++ ".0.") "_private.<M>.0."

structure NormName where
  name : Name
  priv : Bool
  hyg : Bool

def normalizeName (mc : ModCtx) (n : Name) : NormName :=
  let priv := isPrivateName n
  let n1 := privateToUserName n
  let hyg := hasMacroScopeMarker n1
  let n2 := if hyg then stripMacroScopes n1 else n1
  let n3 := if hasAuxDefComponent n2 then
      n2.components.foldl (fun acc c => match c with
        | .str _ s => .str acc (if s.startsWith "_aux_" then normStr mc s else s)
        | .num _ k => .num acc k
        | .anonymous => acc) .anonymous
    else n2
  { name := n3, priv, hyg }

def normName (mc : ModCtx) (n : Name) : Name := (normalizeName mc n).name

/-- Universe parameter names can be hygienic (`v._@.<Module>..._hyg.5`, e.g. in
`noConfusionType` of enumerations); hash them without macro scopes. -/
def hLevelName (n : Name) : UInt64 :=
  hash (if hasMacroScopeMarker n then stripMacroScopes n else n)

partial def hLevel : Level → UInt64
  | .zero => 21
  | .succ l => mix 22 (hLevel l)
  | .max a b => mix 23 (mix (hLevel a) (hLevel b))
  | .imax a b => mix 24 (mix (hLevel a) (hLevel b))
  | .param n => mix 25 (hLevelName n)
  | .mvar m => mix 26 (hash m.name)

def hLevels (ls : List Level) : UInt64 := mixList 27 (ls.map hLevel)

def hBinderInfo : BinderInfo → UInt64
  | .default => 31 | .implicit => 32 | .strictImplicit => 33 | .instImplicit => 34

def hBinderName (n : Name) : UInt64 :=
  hash (if n.hasMacroScopes || hasMacroScopeMarker n then stripMacroScopes n else n)

def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

def mkStrArity? (c : Name) : Option Nat :=
  if c == ``Lean.Name.mkStr1 then some 1 else if c == ``Lean.Name.mkStr2 then some 2
  else if c == ``Lean.Name.mkStr3 then some 3 else if c == ``Lean.Name.mkStr4 then some 4
  else if c == ``Lean.Name.mkStr5 then some 5 else if c == ``Lean.Name.mkStr6 then some 6
  else if c == ``Lean.Name.mkStr7 then some 7 else if c == ``Lean.Name.mkStr8 then some 8
  else none

def isNameCtorHead (c : Name) : Bool :=
  c == ``Lean.Name.mkStr || c == ``Lean.Name.str || c == ``Lean.Name.mkNum ||
  c == ``Lean.Name.num || c == ``Lean.Name.mkSimple || (mkStrArity? c).isSome

/-- Decode a closed `Name` literal expression. -/
partial def nameLit? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    if c == ``Lean.Name.anonymous && args.size == 0 then some .anonymous
    else if (c == ``Lean.Name.mkStr || c == ``Lean.Name.str) && args.size == 2 then do
      let p ← nameLit? args[0]!
      let s ← strLit? args[1]!
      pure (.str p s)
    else if (c == ``Lean.Name.mkNum || c == ``Lean.Name.num) && args.size == 2 then do
      let p ← nameLit? args[0]!
      let k ← natLit? args[1]!
      pure (.num p k)
    else if c == ``Lean.Name.mkSimple && args.size == 1 then do
      let s ← strLit? args[0]!
      pure (.str .anonymous s)
    else match mkStrArity? c with
      | some k =>
        if args.size == k then
          args.foldlM (init := Name.anonymous) fun acc a => do
            let s ← strLit? a
            pure (Name.str acc s)
        else none
      | none => none
  | .mdata _ e => nameLit? e
  | _ => none

structure St where
  cache : Std.HashMap USize UInt64 := {}
  deep : Std.HashMap Name UInt64 := {}
  busy : Std.HashSet Name := {}
  unstable : Std.HashMap Name Bool := {}
  cycles : Nat := 0

abbrev HM := StateM St

structure Ctx where
  env : Environment
  modCtxs : Array ModCtx

def Ctx.modCtxOf (ctx : Ctx) (n : Name) : ModCtx :=
  match ctx.env.getModuleIdxFor? n with
  | some idx => ctx.modCtxs[idx.toNat]!
  | none => ModCtx.ofModule .anonymous

def cachedUnstable (n : Name) : HM Bool := do
  if let some b := (← get).unstable[n]? then return b
  let b := isUnstable n
  modify fun s => { s with unstable := s.unstable.insert n b }
  return b

def kindTag : ConstantInfo → UInt64
  | .axiomInfo _ => 41 | .defnInfo _ => 42 | .thmInfo _ => 43 | .opaqueInfo _ => 44
  | .quotInfo _ => 45 | .inductInfo _ => 46 | .ctorInfo _ => 47 | .recInfo _ => 48

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def lastString (n : Name) : String :=
  match stripMacroScopes (privateToUserName n) with
  | .str _ s => s
  | .num _ k => toString k
  | .anonymous => ""

def hLevelParams (ps : List Name) : UInt64 := mixList 51 (ps.map hLevelName)

mutual

unsafe def hExpr (ctx : Ctx) (mc : ModCtx) (e : Expr) : HM UInt64 := do
  -- Inside a content hash (`busy` is not empty) bound names do not count, so the cache keeps
  -- the two modes apart with the pointer's low bit, which alignment leaves free.
  let inContent := !(← get).busy.isEmpty
  let key := if inContent then ptrAddrUnsafe e ||| 1 else ptrAddrUnsafe e
  if let some h := (← get).cache[key]? then return h
  let hName (n : Name) : UInt64 := if inContent then 19 else hBinderName n
  let h ← match e with
    | .bvar i => pure (mix 1 (UInt64.ofNat i))
    | .sort l => pure (mix 2 (hLevel l))
    | .const n ls => do
      let hn ← hConstRef ctx n
      pure (mix 3 (mix hn (hLevels ls)))
    | .app .. => hApp ctx mc e
    | .lam n t b bi => do
      let ht ← hExpr ctx mc t
      let hb ← hExpr ctx mc b
      pure (mix 4 (mix (hName n) (mix (hBinderInfo bi) (mix ht hb))))
    | .forallE n t b bi => do
      let ht ← hExpr ctx mc t
      let hb ← hExpr ctx mc b
      pure (mix 5 (mix (hName n) (mix (hBinderInfo bi) (mix ht hb))))
    | .letE n t v b nonDep => do
      let ht ← hExpr ctx mc t
      let hv ← hExpr ctx mc v
      let hb ← hExpr ctx mc b
      pure (mix 6 (mixList (hName n) [ht, hv, hb, hBool nonDep]))
    | .lit (.natVal k) => pure (mix 7 (hNat k))
    | .lit (.strVal s) => pure (mix 8 (hStr (normStr mc s)))
    | .mdata _ b => hExpr ctx mc b
    | .proj s i b => do
      let hs ← hConstRef ctx s
      let hb ← hExpr ctx mc b
      pure (mix 9 (mixList hs [UInt64.ofNat i, hb]))
    | .fvar id => pure (mix 10 (hash id.name))
    | .mvar id => pure (mix 11 (hash id.name))
  modify fun s => { s with cache := s.cache.insert key h }
  return h

unsafe def hApp (ctx : Ctx) (mc : ModCtx) (e : Expr) : HM UInt64 := do
  let fn := e.getAppFn
  if let .const c _ := fn then
    if isNameCtorHead c then
      if let some n := nameLit? e then
        return mix 15 (hash (normName mc n))
  let mut h := mix 16 (← hExpr ctx mc fn)
  for a in e.getAppArgs do
    h := mix h (← hExpr ctx mc a)
  return h

/-- Hash of a reference to constant `n`: its name when the name is stable, otherwise its
content. -/
unsafe def hConstRef (ctx : Ctx) (n : Name) : HM UInt64 := do
  if ← cachedUnstable n then deepHash ctx n
  else return mix 12 (hash n)

/-- Content hash of a constant, independent of its name and of bound names: Lean reuses a
matcher within a file when only the bound names differ, so which copy a constant refers to can
change in a merge without changing what it says. -/
unsafe def deepHash (ctx : Ctx) (n : Name) : HM UInt64 := do
  if let some h := (← get).deep[n]? then return h
  if (← get).busy.contains n then
    modify fun s => { s with cycles := s.cycles + 1 }
    return mix 13 (hash (normName (ctx.modCtxOf n) n))
  match ctx.env.find? n with
  | none => return mix 14 (hash (normName (ctx.modCtxOf n) n))
  | some ci =>
    let mc := ctx.modCtxOf n
    if ci.isUnsafe || ci.isPartial then
      -- unsafe and partial constants may be recursive; refer to them by normalized name
      let h := mix 17 (mix (kindTag ci) (hash (normName mc n)))
      modify fun s => { s with deep := s.deep.insert n h }
      return h
    modify fun s => { s with busy := s.busy.insert n }
    let ht ← hExpr ctx mc ci.type
    let base := mixList (kindTag ci) [hLevelParams ci.levelParams, ht]
    let h ← match ci with
      | .defnInfo v => do pure (mix base (← hExpr ctx mc v.value))
      | .opaqueInfo v => do pure (mix base (← hExpr ctx mc v.value))
      | .inductInfo v =>
        pure (mixList base ([hNat v.numParams, hNat v.numIndices, hBool v.isRec,
          hNat v.all.length] ++ v.ctors.map (fun c => hStr (lastString c))))
      | .ctorInfo v => pure (mixList base [hNat v.cidx, hNat v.numParams, hNat v.numFields])
      | _ => pure base
    modify fun s => { s with deep := s.deep.insert n h, busy := s.busy.erase n }
    return h

end

def keyName (mc : ModCtx) (n : Name) : String := (normName mc n).toString

unsafe def valueHash (ctx : Ctx) (mc : ModCtx) (ci : ConstantInfo) : HM (Option UInt64) := do
  match ci with
  | .thmInfo _ => return none
  | .defnInfo v =>
    let hv ← hExpr ctx mc v.value
    let hints : UInt64 := match v.hints with
      | .opaque => 61 | .abbrev => 62 | .regular k => mix 63 (UInt64.ofNat k.toNat)
    let safety : UInt64 := match v.safety with
      | .safe => 64 | .unsafe => 65 | .partial => 66
    return some (mixList 60 [hv, hints, safety])
  | .opaqueInfo v =>
    return some (mixList 67 [← hExpr ctx mc v.value, hBool v.isUnsafe])
  | .axiomInfo v => return some (mix 68 (hBool v.isUnsafe))
  | .quotInfo v =>
    return some (mix 69 (match v.kind with | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4))
  | .inductInfo v =>
    return some (mixList 70 ([hNat v.numParams, hNat v.numIndices, hBool v.isRec,
      hBool v.isUnsafe, hBool v.isReflexive, hNat v.numNested, hNat v.all.length] ++
      v.ctors.map (fun c => hStr (lastString c))))
  | .ctorInfo v =>
    return some (mixList 71 [hNat v.cidx, hNat v.numParams, hNat v.numFields, hBool v.isUnsafe])
  | .recInfo v =>
    let mut h := mixList 72 [hNat v.numParams, hNat v.numIndices, hNat v.numMotives,
      hNat v.numMinors, hBool v.k, hBool v.isUnsafe, hNat v.all.length]
    for r in v.rules do
      h := mixList h [hStr (lastString r.ctor), hNat r.nfields, ← hExpr ctx mc r.rhs]
    return some h

structure SimpExts where
  exts : Array (Name × SimpTheorems)

def flagsOf (env : Environment) (simps : SimpExts) (n : Name) (nn : NormName) : Array String := Id.run do
  let mut fs : Array String := #[]
  if nn.priv then fs := fs.push "private"
  if nn.hyg then fs := fs.push "hygienic"
  if let some e := (Meta.instanceExtension.getState env).instanceNames.find? n then
    fs := fs.push s!"instance:{e.priority}"
  for (attr, st) in simps.exts do
    if st.lemmaNames.contains (.decl n) then fs := fs.push s!"{attr}"
    if st.lemmaNames.contains (.decl n (inv := true)) then fs := fs.push s!"{attr}:inv"
    if st.toUnfold.contains n then fs := fs.push s!"{attr}:unfold"
  match getReducibilityStatusCore env n with
  | .semireducible => pure ()
  | .reducible => fs := fs.push "reducible"
  | .irreducible => fs := fs.push "irreducible"
  | .implicitReducible => fs := fs.push "implicit_reducible"
  | .instanceReducible => fs := fs.push "instance_reducible"
  if isProtected env n then fs := fs.push "protected"
  if isNoncomputable env n then fs := fs.push "noncomputable"
  if isClass env n then fs := fs.push "class"
  if let some k := Compiler.getInlineAttribute? env n then
    fs := fs.push (match k with
      | .inline => "inline" | .noinline => "noinline" | .macroInline => "macro_inline"
      | .inlineIfReduce => "inline_if_reduce" | .alwaysInline => "always_inline")
  if let some t := Compiler.getImplementedBy? env n then
    fs := fs.push s!"implemented_by:{normName (ModCtx.ofModule .anonymous) t}"
  if isExtern env n then fs := fs.push "extern"
  if let some d := docStringExt.find? (level := .server) env n then
    fs := fs.push s!"doc:{hex (hash d)}"
  return fs

structure Out where
  lines : Array String := #[]
  skipped : Array String := #[]

unsafe def processModules (env : Environment) (modCtxs : Array ModCtx) (simps : SimpExts)
    (mods : Array Nat) : Out × Nat := Id.run do
  let ctx : Ctx := { env, modCtxs }
  let mut out : Out := {}
  let mut st : St := {}
  for idx in mods do
    let mc := modCtxs[idx]!
    let data := env.header.moduleData[idx]!
    -- per-module pointer cache: subterm sharing does not cross module regions
    st := { st with cache := {} }
    for n in data.constNames do
      -- realized constants can be stored in several modules; keep the first one
      if (env.getModuleIdxFor? n).map (·.toNat) != some idx then continue
      let some ci := env.find? n | continue
      if let some why := skipReason? (privateToUserName n) then
        out := { out with skipped := out.skipped.push s!"{n}\t{why}\t{mc.mod}" }
        continue
      let nn := normalizeName mc n
      let ((th, vh), st') := (do
          let ht ← hExpr ctx mc ci.type
          let vh ← valueHash ctx mc ci
          pure (mix (hLevelParams ci.levelParams) ht, vh)).run st
      st := st'
      let flags := flagsOf env simps n nn
      let mut fields : List (String × Json) :=
        [("n", Json.str nn.name.toString), ("k", Json.str (kindName ci)), ("t", Json.str (hex th))]
      if let some v := vh then fields := fields ++ [("v", Json.str (hex v))]
      fields := fields ++ [("f", Json.arr (flags.map Json.str)), ("m", Json.str mc.dotted)]
      out := { out with lines := out.lines.push (Json.mkObj fields).compress }
  return (out, st.cycles)

def readGroups (path : System.FilePath) : IO (Array (Array Name)) := do
  let mut groups : Array (Array Name) := #[]
  let mut cur : Array Name := #[]
  for l in ← IO.FS.lines path do
    let l := l.trimAscii.toString
    if l == "---" then
      unless cur.isEmpty do groups := groups.push cur
      cur := #[]
    else if !l.isEmpty && !l.startsWith "#" then
      cur := cur.push l.toName
  unless cur.isEmpty do groups := groups.push cur
  return groups

end DeclSnapshot

open DeclSnapshot in
unsafe def main (args : List String) : IO UInt32 := do
  let some (groupsFile : String) := args[0]? | do IO.eprintln "usage: DeclSnapshot <groups.txt> <out.jsonl> [threads]"; return 2
  let some (outFile : String) := args[1]? | do IO.eprintln "usage: DeclSnapshot <groups.txt> <out.jsonl> [threads]"; return 2
  let threads := (args[2]? >>= String.toNat?).getD 8
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let groups ← readGroups groupsFile
  let h ← IO.FS.Handle.mk outFile .write
  let hs ← IO.FS.Handle.mk (outFile ++ ".skipped.tsv") .write
  let mut total := 0
  let mut skippedTotal := 0
  for g in groups do
    let t0 ← IO.monoMsNow
    let env ← importModules (g.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    let t1 ← IO.monoMsNow
    let modCtxs := env.header.moduleNames.map ModCtx.ofModule
    let want : Std.HashSet Name := g.foldl (·.insert ·) {}
    let mut owned : Array Nat := #[]
    for i in [0:env.header.moduleNames.size] do
      if want.contains env.header.moduleNames[i]! then owned := owned.push i
    let simpMap ← simpExtensionMapRef.get
    let mut exts : Array (Name × SimpTheorems) := #[]
    for (attr, ext) in simpMap.toList do
      exts := exts.push (attr, ext.getState env)
    exts := exts.qsort (fun a b => a.1.lt b.1)
    let simps : SimpExts := { exts }
    -- split owned modules into chunks by constant count, process chunks in parallel
    let nChunks := max 1 (min threads owned.size)
    let mut chunks : Array (Array Nat) := Array.replicate nChunks #[]
    let mut loads : Array Nat := Array.replicate nChunks 0
    let sorted := owned.qsort (fun a b =>
      env.header.moduleData[a]!.constNames.size > env.header.moduleData[b]!.constNames.size)
    for idx in sorted do
      let mut best := 0
      for j in [0:nChunks] do
        if loads[j]! < loads[best]! then best := j
      chunks := chunks.modify best (·.push idx)
      loads := loads.modify best (· + env.header.moduleData[idx]!.constNames.size + 1)
    let tasks := chunks.map fun ch => Task.spawn (prio := .dedicated) fun _ => processModules env modCtxs simps ch
    let mut cycles := 0
    let mut n := 0
    let mut sk := 0
    for t in tasks do
      let (out, c) := t.get
      cycles := cycles + c
      for l in out.lines do h.putStrLn l
      for l in out.skipped do hs.putStrLn l
      n := n + out.lines.size
      sk := sk + out.skipped.size
    let t2 ← IO.monoMsNow
    IO.eprintln s!"group of {g.size} modules ({env.header.moduleNames.size} imported): import {t1 - t0} ms, hash {t2 - t1} ms, {n} constants written, {sk} skipped, {cycles} cycles"
    total := total + n
    skippedTotal := skippedTotal + sk
  h.flush
  hs.flush
  IO.eprintln s!"total: {total} constants written, {skippedTotal} skipped"
  return 0
