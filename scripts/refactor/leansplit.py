#!/usr/bin/env python3
"""leansplit: split a Lean module without changing any declaration.

Run from the repository (worktree) root, or pass --root.

  leansplit.py check [--area P]                  round-trip every file (self-test)
  leansplit.py scan FILE...                      how a file is read: items, scopes, names
  leansplit.py refs MODULE                       each declaration and the file's private names it mentions
  leansplit.py extract M --into N --names F      N sits below M
  leansplit.py peel M --into N --names F         N sits above M

Both commands move the declarations listed in F (full names, one per line, `#` comments) from M
to the new module N, in source order. A declaration keeps its doc comment, its attributes and any
`set_option ... in` or `open ... in` prefix. Each part gets the namespaces, sections, `open`,
`variable`, `universe` and `set_option` commands that its declarations need.

extract: M keeps the rest and gains `import N`. N gets M's imports, or those in --imports FILE,
which is how definitions leave a file that also imports proofs. Importers of M are untouched.

peel: N imports M and all of M's imports. M keeps the rest and its imports, or those in --imports
FILE. Importers of M inside --area are rewritten to import N, apart from those in
--keep-importers FILE, so their closure does not change. Importers outside the area keep M; check
them.

A mention across the cut of a private name stops the command, because `private` is per file. The
check is textual and compares the last component of each identifier, so it can report a local
variable that shares a helper's name. Name such a mention with --ignore NAME, or list the
declaration so that it moves too.

--doc TEXT adds a file-level module doc to N. A split is recorded as a `# split` comment line in
the moves file, because the module M still exists.

The parser reads commands at column 0, which is what `leanmerge.py` also requires of scope
commands. `check` shows that it reads a tree: rendering every declaration of a file must return
the file's own commands in order.
"""
import argparse, collections, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import leanmerge as lm

COMMAND = re.compile(
    r"(?:private|protected|public|noncomputable|partial|unsafe|nonrec|theorem|lemma|def|abbrev|"
    r"instance|structure|class|inductive|axiom|opaque|example|namespace|section|end|open|export|"
    r"universe|variable|set_option|attribute|mutual|macro|syntax|notation|infixl|infixr|infix|"
    r"prefix|postfix|elab|local|scoped|initialize|deriving\s+instance)\b|@\[|#[a-zA-Z]")
SCOPE = re.compile(r"(?:noncomputable[ \t]+)?(namespace|section|end|mutual)\b[ \t]*([^\s]*)")
CONTEXT = re.compile(r"(?:open|variable|universe|set_option)\b")
PREFIX_ONLY = re.compile(r"(?:(?:@\[[^\n]*\]|private|protected|public|noncomputable|partial|unsafe|nonrec|"
                         r"local|scoped)\s*)+$")
INDENTED = re.compile(r"[ \t]+(?:(?:private|protected|noncomputable)[ \t]+)*"
                      r"(?:theorem|lemma|def|abbrev|structure|inductive)\b")
TOKEN = re.compile(r"[A-Za-z_Ͱ-Ͽ«][\w.'!?«»Ͱ-Ͽ]*")


class Scope:
    def __init__(self, parent, open_text, comps):
        self.parent, self.open_text, self.comps = parent, open_text, comps
        self.close_text = None
        self.context = []   # context items, in source order

    def chain(self):
        out, s = [], self
        while s is not None:
            out.append(s)
            s = s.parent
        return out[::-1]


class Item:
    def __init__(self, kind, start, end, text, scope, order):
        self.kind, self.start, self.end, self.text = kind, start, end, text
        self.scope, self.order = scope, order
        self.names = []     # full names declared here
        self.private = []   # those of them that are private


class Parsed:
    pass


def chunks(text, masked, comments, begin):
    """Column-0 starts of commands and comments, as (offset, kind)."""
    comment_at = {s: (e, k) for s, e, k in comments}
    spans = sorted((s, e) for s, e, _ in comments)
    out, p, n, ci = [], begin, len(text), 0
    blank = True
    while p < n:
        while ci < len(spans) and spans[ci][1] <= p:
            ci += 1
        inside = ci < len(spans) and spans[ci][0] < p < spans[ci][1]
        c = text[p]
        q = text.find("\n", p)
        line_end = n if q < 0 else q
        if not inside and c not in " \t\n\r":
            if p in comment_at:
                out.append((p, comment_at[p][1]))
            elif COMMAND.match(masked, p):
                out.append((p, "command"))
        elif not inside and c in " \t" and blank and INDENTED.match(masked, p):
            out.append((p, "command"))     # a declaration indented after a blank line
        blank = not text[p:line_end].strip()
        if q < 0:
            break
        p = q + 1
    return out


def parse(text):
    """Split a file into items. Raises ValueError on a shape it does not read."""
    h = lm.parse_header(text)
    masked, comments = lm.mask(text)
    begin = h.end
    starts = chunks(text, masked, comments, begin)
    res = Parsed()
    res.text, res.header_end, res.items = text, begin, []
    res.head = text[:begin]
    root = Scope(None, "", [])
    res.root = root
    scope = root
    pending = None              # start of glued prefix (comments, attributes, `... in`)
    filedoc_open = True
    i, n = 0, len(starts)
    bounds = [s for s, _ in starts] + [len(text)]
    order = 0

    def add(kind, s, e, sc):
        nonlocal order
        it = Item(kind, s, e, text[s:e].rstrip(), sc, order)
        order += 1
        res.items.append(it)
        return it

    while i < n:
        s, k = starts[i]
        e = bounds[i + 1]
        m_text = masked[s:e]
        if k == "moddoc" and filedoc_open and pending is None and scope is root:
            add("filedoc", s, e, root)
            i += 1
            continue
        if k != "command":
            if text.startswith("-- leanmerge: from ", s) and res.items and res.items[-1].kind == "open":
                res.items[-1].text += "\n" + text[s:e].rstrip()
                res.items[-1].end = e
                scope.open_text = res.items[-1].text
                i += 1
                continue
            pending = s if pending is None else pending
            i += 1
            continue
        stripped = m_text.strip()
        if PREFIX_ONLY.match(stripped) or re.search(r"\bin\s*$", stripped) and CONTEXT.match(stripped):
            pending = s if pending is None else pending
            i += 1
            continue
        sm = SCOPE.match(masked, s)
        kw = sm.group(1) if sm else None
        name = sm.group(2) if sm else ""
        if name.startswith("--") or name.startswith("/-"):
            name = ""
        if kw in ("namespace", "section"):
            start = pending if pending is not None else s
            pending = None
            filedoc_open = False
            comps = lm.split_name(name) if kw == "namespace" else ([name] if name else [""])
            child = Scope(scope, text[start:e].rstrip(), comps)
            it = add("open", start, e, scope)
            it.scope_obj = child
            scope = child
            i += 1
            continue
        if kw == "end":
            start = pending if pending is not None else s
            pending = None
            comps = lm.split_name(name) if name else [""]
            closed = []
            while comps:
                if scope is root:
                    raise ValueError(f"line {text.count(chr(10), 0, s) + 1}: `end {name}` with no open scope")
                k = len(scope.comps)
                if len(comps) >= k and comps[-k:] == scope.comps:
                    comps = comps[:-k]
                    closed.append(scope)
                    scope = scope.parent
                elif len(comps) < k and scope.comps[-len(comps):] == comps:
                    # `end B` inside `namespace A.B`: read it as two nested scopes
                    head, tail = scope.comps[:-len(comps)], comps
                    outer = Scope(scope.parent, "namespace " + ".".join(head), head)
                    scope.parent, scope.comps = outer, tail
                    scope.open_text = "namespace " + ".".join(tail)
                    closed.append(scope)
                    scope, comps = outer, []
                else:
                    raise ValueError(f"line {text.count(chr(10), 0, s) + 1}: `end {name}` does not match "
                                     f"{'.'.join(scope.comps)}")
            for sc in closed:
                sc.close_text = text[start:e].rstrip() if len(closed) == 1 else "end " + ".".join(sc.comps)
            add("close", start, e, closed[-1])
            i += 1
            continue
        if kw == "mutual":
            start = pending if pending is not None else s
            pending = None
            j, depth = i + 1, 1
            while j < n:
                ss, kk = starts[j]
                if kk == "command":
                    m2 = SCOPE.match(masked, ss)
                    if m2 and m2.group(1) == "end":
                        depth -= 1
                        if depth == 0:
                            break
                    elif m2 and m2.group(1) == "mutual":
                        depth += 1
                j += 1
            if j >= n:
                raise ValueError(f"offset {s}: `mutual` without `end`")
            it = add("decl", start, bounds[j + 1], scope)
            filedoc_open = False
            i = j + 1
            continue
        if CONTEXT.match(masked, s):
            start = pending if pending is not None else s
            pending = None
            it = add("context", start, e, scope)
            scope.context.append(it)
            i += 1
            continue
        start = pending if pending is not None else s
        pending = None
        add("decl", start, e, scope)
        filedoc_open = False
        i += 1
    if pending is not None:
        add("trailer", pending, len(text), scope)
    a = lm.Analysis(text, start=begin)
    res.analysis = a
    decl_items = [it for it in res.items if it.kind in ("decl", "trailer")]
    idx = 0
    for off, full, priv, kw in a.decls:
        while idx < len(decl_items) and decl_items[idx].end <= off:
            idx += 1
        if idx < len(decl_items) and decl_items[idx].start <= off:
            decl_items[idx].names.append(full)
            if priv:
                decl_items[idx].private.append(full)
    return res


def render(parsed, picked):
    """The body holding the items in `picked` (a set of item orders), with the scopes they need."""
    out = []
    for it in parsed.items:
        if it.kind == "filedoc":
            out.append(it.text)
    stack = []                  # scopes currently open in the output
    done = set()                # context items already written
    items = [it for it in parsed.items if it.order in picked]
    for it in items:
        chain = it.scope.chain()[1:]
        common = 0
        while common < len(stack) and common < len(chain) and stack[common] is chain[common]:
            common += 1
        while len(stack) > common:
            sc = stack.pop()
            if sc.close_text:
                out.append(sc.close_text)
        emit_ctx(parsed.root, it, done, out)
        for sc in chain[:common]:
            emit_ctx(sc, it, done, out)
        for sc in chain[common:]:
            out.append(sc.open_text)
            stack.append(sc)
            emit_ctx(sc, it, done, out)
        out.append(it.text)
    while stack:
        sc = stack.pop()
        if sc.close_text:
            out.append(sc.close_text)
    return "\n\n".join(out) + "\n"


def emit_ctx(scope, upto, done, out):
    for c in scope.context:
        if c.order < upto.order and c.order not in done:
            done.add(c.order)
            out.append(c.text)


def mentions(masked_text):
    return {t.split(".")[-1] for t in TOKEN.findall(masked_text)}


def check_file(path):
    """Refuse a file unless the items cover it, and rendering them keeps every declaration in
    order with the context commands in front of it. Returns the problem, or None."""
    text = open(path, encoding="utf-8").read()
    try:
        p = parse(text)
    except ValueError as e:
        return str(e)
    pos = p.header_end
    for it in p.items:
        if text[pos:it.start].strip():
            return f"line {text.count(chr(10), 0, pos) + 1}: text outside any item"
        pos = max(pos, it.end)
    if text[pos:].strip():
        return f"line {text.count(chr(10), 0, pos) + 1}: text outside any item"
    decls = [it for it in p.items if it.kind in ("decl", "trailer")]
    body = render(p, {it.order for it in decls})
    pos = 0
    for it in decls:
        q = body.find(it.text, pos)
        if q < 0:
            return f"declaration lost: {it.text[:60]!r}"
        pos = q + len(it.text)
    last = decls[-1].order if decls else -1
    for it in p.items:
        if it.kind == "context" and it.order < last and it.text not in body:
            below = it.scope.chain()
            if any(d.order > it.order and below == d.scope.chain()[:len(below)] for d in decls):
                return f"context lost: {it.text[:60]!r}"
    n_decls = sum(len(it.names) for it in p.items)
    if n_decls != len(p.analysis.decls):
        return f"{len(p.analysis.decls) - n_decls} declarations not attached to an item"
    return None


def read_list(path):
    if path is None:
        return None
    out = []
    for l in open(path, encoding="utf-8"):
        l = l.split("#", 1)[0].strip()
        if l:
            out.append(l)
    return out


def resolve_names(parsed, names, module):
    by_name = {}
    for it in parsed.items:
        for f in it.names:
            by_name[f] = it
    picked, missing = set(), []
    for n in names:
        if n in by_name:
            picked.add(by_name[n].order)
        else:
            missing.append(n)
    if missing:
        sys.exit(f"{module}: not declared here: {', '.join(missing[:8])}")
    return picked


def private_crossings(parsed, picked, ignore):
    """Mentions across the cut of a name that is private to the file."""
    moved = [it for it in parsed.items if it.order in picked]
    stay = [it for it in parsed.items if it.kind in ("decl", "trailer") and it.order not in picked]
    masked = parsed.analysis.masked
    def last(names):
        return {n.split(".")[-1]: n for n in names}
    moved_priv = last([n for it in moved for n in it.private])
    stay_priv = last([n for it in stay for n in it.private])
    out = []
    for group, other in ((moved, stay_priv), (stay, moved_priv)):
        for it in group:
            own = {n.split(".")[-1] for n in it.names}
            hit = (mentions(masked[it.start:it.end]) & set(other)) - own - set(ignore)
            for h in sorted(hit):
                out.append((it.names[0] if it.names else f"item at {it.start}", other[h]))
    return out


def with_header(imports, body):
    head = "".join(f"import {i}\n" for i in imports)
    return head + "\n" + body if body.strip() else head


def with_doc(body, doc):
    if not doc:
        return body
    return f"/-!\n{doc.strip()}\n-/\n\n" + body


def split(args, mode):
    repo = lm.Repo(args.root, args.moves)
    m, n = args.module, args.into
    if m not in repo.paths:
        sys.exit(f"{m}: no such module")
    if m in repo.shims:
        sys.exit(f"{m}: is a refactor shim")
    if n in repo.paths:
        sys.exit(f"{n}: exists")
    t = repo.text(m)
    h = lm.parse_header(t)
    if h.module_system or h.modifiers or h.prelude:
        sys.exit(f"{m}: uses the module system or `prelude`")
    problem = check_file(os.path.join(repo.root, repo.paths[m]))
    if problem:
        sys.exit(f"{m}: refused, the file does not round-trip: {problem}")
    parsed = parse(t)
    picked = resolve_names(parsed, read_list(args.names), m)
    crossing = private_crossings(parsed, picked, args.ignore or [])
    if crossing:
        for who, what in crossing[:12]:
            print(f"refused: {who} mentions {what}, which is private to {m} and on the other side", file=sys.stderr)
        sys.exit(f"refused: {len(crossing)} private mention(s) across the cut")
    rest = {it.order for it in parsed.items if it.kind in ("decl", "trailer")} - picked
    old_imports = [x[0] for x in h.imports]
    given = read_list(args.imports)
    new_body = with_doc(render(parsed, picked), args.doc)
    old_body = render(parsed, rest)
    if mode == "extract":
        new_imports = given if given is not None else old_imports
        new_text = with_header(new_imports, new_body)
        old_text = with_header([n] + old_imports, old_body)
    else:
        new_imports = [m] + [i for i in old_imports if i != m]
        new_text = with_header(new_imports, new_body)
        kept = given if given is not None else old_imports
        old_text = with_header(kept, old_body)
    dry = args.dry_run
    print(f"{'would write' if dry else 'wrote'} {lm.module_to_path(n)}: {len(picked)} items, "
          f"{new_text.count(chr(10))} lines; {repo.paths[m]} keeps {len(rest)} items, {old_text.count(chr(10))} lines")
    repo.write(n, new_text, dry)
    repo.write(m, old_text, dry)
    if mode == "peel":
        keep = set(read_list(args.keep_importers) or [])
        for imp in sorted(repo.importers.get(m, ())):
            if imp == n or imp in keep:
                continue
            if lm.in_area(repo.paths[imp], args.area):
                new, changed = lm.rewrite_imports(repo.text(imp), {m: n}, self_module=imp)
                if changed:
                    repo.write(imp, new, dry)
                    print(f"  rewrote imports of {repo.paths[imp]}")
            else:
                print(f"  note: {imp} is outside the area and still imports {m}")
    if not dry:
        os.makedirs(os.path.dirname(repo.moves_path), exist_ok=True)
        new_file = not os.path.exists(repo.moves_path)
        with open(repo.moves_path, "a", encoding="utf-8") as f:
            if new_file:
                f.write("# old_module\tnew_module\tkind\n")
            f.write(f"# split\t{m}\t{n}\t{mode}\n")


def cmd_check(args):
    repo = lm.Repo(args.root)
    bad = 0
    mods = [m for m, p in repo.paths.items() if not args.area or lm.in_area(p, args.area)]
    for m in sorted(mods):
        r = check_file(os.path.join(repo.root, repo.paths[m]))
        if r:
            bad += 1
            print(f"{repo.paths[m]}: {r}")
    print(f"{len(mods)} files read, {bad} refused")
    sys.exit(1 if bad else 0)


def cmd_scan(args):
    for f in args.files:
        p = parse(open(f, encoding="utf-8").read())
        print(f"== {f}: {len(p.items)} items")
        for it in p.items:
            line = p.text.count("\n", 0, it.start) + 1
            depth = len(it.scope.chain()) - 1
            label = ", ".join(n + (" (private)" if n in it.private else "") for n in it.names[:3])
            first = it.text.splitlines()[0][:60] if it.text else ""
            print(f"  {line:5} {'  ' * depth}{it.kind:8} {label or first}")


def cmd_refs(args):
    repo = lm.Repo(args.root)
    p = parse(repo.text(args.module))
    masked = p.analysis.masked
    priv = {n.split(".")[-1]: n for it in p.items for n in it.private}
    for it in p.items:
        if it.kind != "decl" or not it.names:
            continue
        own = {n.split(".")[-1] for n in it.names}
        hit = sorted((mentions(masked[it.start:it.end]) & set(priv)) - own)
        tag = "private" if it.private else "public"
        print(f"{it.names[0]}\t{tag}\t{it.text.count(chr(10)) + 1}\t{' '.join(hit)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--moves", help="moves file (default <root>/.refactor/moves.tsv)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("--area")
    s = sub.add_parser("scan")
    s.add_argument("files", nargs="+")
    r = sub.add_parser("refs")
    r.add_argument("module")
    for name in ("extract", "peel"):
        x = sub.add_parser(name)
        x.add_argument("module")
        x.add_argument("--into", required=True)
        x.add_argument("--names", required=True)
        x.add_argument("--area", required=True)
        x.add_argument("--imports")
        x.add_argument("--doc")
        x.add_argument("--ignore", action="append")
        x.add_argument("--dry-run", action="store_true")
        if name == "peel":
            x.add_argument("--keep-importers")
    args = ap.parse_args()
    if args.cmd == "check":
        cmd_check(args)
    elif args.cmd == "scan":
        cmd_scan(args)
    elif args.cmd == "refs":
        cmd_refs(args)
    else:
        split(args, args.cmd)


if __name__ == "__main__":
    main()
