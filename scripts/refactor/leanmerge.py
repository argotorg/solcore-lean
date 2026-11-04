#!/usr/bin/env python3
"""leanmerge: merge and move Lean modules without changing any declaration.

Run from the repository (worktree) root, or pass --root.

  leanmerge.py graph [--area P] [--top N]                 import-graph statistics
  leanmerge.py graph --importers M [--transitive] [--area P]
  leanmerge.py graph --imports M [--transitive]
  leanmerge.py graph --area P --chains|--siblings [--min-group K] [--max-lines L]
  leanmerge.py merge --into T --area P [--dry-run] M1 ... Mn
  leanmerge.py move OLD NEW --area P [--dry-run]
  leanmerge.py consolidate [--dry-run] [--ext md,py,mjs]
  leanmerge.py clashes [--area P] [--top N]              duplicate names among files of a directory
  leanmerge.py scan FILE...                              debug: declarations and closing `end`s

merge writes T with the union of the sources' imports (resolved through recorded moves,
minus the group) and each source body in its own `section` ... `end` (module doc first,
`end`s added for namespaces/sections the body leaves open), in topological order of the
sources' imports, otherwise in the given order. If T exists, the new bodies go before or
after its content as the imports require. Importers of a source inside the area are
rewritten to import T; a source with importers outside the area is left as a shim.
Refusals: module-system files, lakefile roots, shims as sources, `#exit`, unbalanced or
indented scope commands, an import cycle through a module outside the group, and any name
declared in two bodies (private clash; when the two declarations are textually identical the
message says which copy to delete). Warnings: an earlier body's instances, simp lemmas or
notations become visible to a later body that did not import it; two bodies declare a
notation with the same leading atom in the same namespace.

move: the same for one module; the file is copied verbatim apart from resolved imports.
consolidate: rewrites every import of a shim or moved module to its final target (chains
A -> B -> C resolved), deletes the shims, and rewrites paths `Solcore/A/B.lean` and module
names `Solcore.A.B` (not `Solcore.A.B.decl`) in *.md, *.py and *.mjs files.

State: moves are appended to <root>/.refactor/moves.tsv (or the file given with --moves, e.g.
.refactor/moves-<lane>.tsv so that parallel lanes never edit the same file); every
.refactor/moves*.tsv is read. The tool never touches the git index. Shims contain only
`import <target>` and the marker line `-- refactor shim`.

Area: a module is inside --area P when its path is P.lean or lies under P/.
"""
import argparse, collections, os, re, subprocess, sys

SHIM_MARKER = "-- refactor shim"
FROM_MARKER = "-- leanmerge: from "

# ======================================================================= lexing

def is_ident_char(c):
    return c.isalnum() or c in "_'!?"


_TOK = re.compile(r"--|/-|\"|'|«|(?<![\w'!?])r#*\"")
_BLOCK = re.compile(r"/-|-/")
_STR_BODY = re.compile(r'(?:[^"\\]|\\.)*"', re.S)
_CHAR_LIT = re.compile(r"'(?:\\(?:[\\'\"ntr0]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\})|[^\\'\n])'")
_NONNL = re.compile(r"[^\n]")


def _blank(s):
    return _NONNL.sub(" ", s)


def mask(text):
    """Return (masked, comments): masked has comments and string/char contents replaced
    by spaces (newlines kept, so offsets and columns are unchanged). comments is a list of
    (start, end, kind) with kind in line/block/doc/moddoc."""
    out, comments = [], []
    pos = i = 0
    n = len(text)
    while True:
        m = _TOK.search(text, i)
        if not m:
            break
        s, t = m.start(), m.group()
        if t == "--":
            e = text.find("\n", s)
            e = n if e < 0 else e
            comments.append((s, e, "line"))
            out += [text[pos:s], _blank(text[s:e])]
            pos = i = e
        elif t == "/-":
            depth, j = 1, s + 2
            while depth:
                mm = _BLOCK.search(text, j)
                if not mm:
                    j = n
                    break
                j = mm.end()
                depth += 1 if mm.group() == "/-" else -1
            kind = "moddoc" if text.startswith("/-!", s) else "doc" if text.startswith("/--", s) else "block"
            comments.append((s, j, kind))
            out += [text[pos:s], _blank(text[s:j])]
            pos = i = j
        elif t == '"':
            mm = _STR_BODY.match(text, s + 1)
            e = mm.end() if mm else n
            out += [text[pos:s + 1], _blank(text[s + 1:e - 1])]
            pos = e - 1
            i = e
        elif t == "'":
            if s > 0 and is_ident_char(text[s - 1]):
                i = s + 1
                continue
            mm = _CHAR_LIT.match(text, s)
            if mm:
                out += [text[pos:s + 1], _blank(text[s + 1:mm.end() - 1])]
                pos = mm.end() - 1
                i = mm.end()
            else:
                i = s + 1
        elif t == "«":
            e = text.find("»", s)
            i = n if e < 0 else e + 1
        else:  # raw string r#"..."#
            hashes = t.count("#")
            close = '"' + "#" * hashes
            e = text.find(close, m.end())
            e = n if e < 0 else e + len(close)
            out += [text[pos:m.end()], _blank(text[m.end():e - len(close)])]
            pos = e - len(close)
            i = e
    out.append(text[pos:])
    masked = "".join(out)
    assert len(masked) == len(text)
    return masked, comments


# ======================================================================= header

_WS = re.compile(r"\s*")
_IMPORT = re.compile(r"((?:(?:public|meta|private)[ \t]+)*)import[ \t]+(?:all[ \t]+)?([^\s]+)")


class Header:
    def __init__(self):
        self.imports = []          # (module, name_start, name_end, stmt_start, line_end)
        self.module_system = False
        self.prelude = False
        self.first_import = None   # offset of first `import` (or None)
        self.end = 0               # offset just after the last import line (0 if none)
        self.modifiers = False     # public/meta/private import modifiers


def parse_header(text):
    h = Header()
    i, n = 0, len(text)
    while i < n:
        i = _WS.match(text, i).end()
        if text.startswith("--", i):
            e = text.find("\n", i)
            i = n if e < 0 else e + 1
            continue
        if text.startswith("/-", i):
            if text.startswith("/-!", i) or text.startswith("/--", i):
                break
            depth, j = 1, i + 2
            while depth:
                mm = _BLOCK.search(text, j)
                if not mm:
                    j = n
                    break
                j = mm.end()
                depth += 1 if mm.group() == "/-" else -1
            i = j
            continue
        m = _IMPORT.match(text, i)
        if m:
            if m.group(1).strip():
                h.modifiers = True
            if h.first_import is None:
                h.first_import = i
            e = text.find("\n", m.end())
            e = n if e < 0 else e + 1
            h.imports.append((m.group(2), m.start(2), m.end(2), i, e))
            h.end = e
            i = m.end()
            continue
        if re.match(r"prelude\b", text[i:i + 8]):
            h.prelude = True
            i += 7
            continue
        if re.match(r"module\b", text[i:i + 7]):
            h.module_system = True
            i += 6
            continue
        break
    return h


def rewrite_imports(text, mapping, self_module=None, extra=()):
    """Rewrite header imports: mapping old -> new (None deletes). Duplicates and self-imports
    are dropped. `extra` modules are appended after the last import if not present."""
    h = parse_header(text)
    seen, pieces, pos, changed = set(), [], 0, False
    for (mod, ns, ne, ss, le) in h.imports:
        new = mapping.get(mod, mod)
        if new is None or new in seen or new == self_module:
            # drop the statement; drop the whole line if nothing else remains on it
            line_start = text.rfind("\n", 0, ss) + 1
            rest = text[ne:le]
            before = text[line_start:ss]
            if before.strip() == "" and rest.strip() == "":
                pieces.append(text[pos:line_start])
                pos = le
            else:
                pieces.append(text[pos:ss])
                pos = ne
            changed = True
            continue
        seen.add(new)
        if new != mod:
            pieces.append(text[pos:ns])
            pieces.append(new)
            pos = ne
            changed = True
    add = [m for m in extra if m not in seen and m != self_module]
    if add:
        at = h.end
        pieces.append(text[pos:at])
        if at > 0 and not text[:at].endswith("\n"):
            pieces.append("\n")
        pieces.append("".join(f"import {m}\n" for m in add))
        pos = at
        changed = True
    pieces.append(text[pos:])
    return "".join(pieces), changed


# ======================================================================= scopes and declarations

_SCOPE = re.compile(r"^(?:(noncomputable)[ \t]+)?(namespace|section|end|mutual)\b[ \t]*([^\s]*)", re.M)
_INDENTED_SCOPE = re.compile(r"^[ \t]+(?:noncomputable[ \t]+)?(namespace|section|end|mutual)\b", re.M)
_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\n]*?\][ \t]*)?"
    r"(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)[ \t]+)*)"
    r"(?P<kw>def|theorem|lemma|abbrev|instance|structure|class[ \t]+inductive|class|inductive|axiom|opaque|irreducible_def)\b"
    r"(?P<rest>[^\n]*)", re.M)
_NOTATION = re.compile(
    r"^[ \t]*(?:@\[[^\n]*?\][ \t]*)?(?P<mods>(?:(?:local|scoped|private)[ \t]+)*)"
    r"(?P<kw>notation|infixl|infixr|infix|prefix|postfix|macro_rules|macro|syntax|elab_rules|elab|"
    r"declare_syntax_cat|unif_hint)\b(?P<rest>[^\n]*)", re.M)
_GLOBAL_ATTR = re.compile(r"^[ \t]*attribute[ \t]*\[(?P<attrs>[^\]\n]*)\]", re.M)
_EXIT = re.compile(r"^[ \t]*#exit\b", re.M)


def split_name(name):
    """Split a dotted identifier respecting «...»."""
    parts, cur, i = [], "", 0
    while i < len(name):
        c = name[i]
        if c == "«":
            j = name.find("»", i)
            j = len(name) - 1 if j < 0 else j
            cur += name[i:j + 1]
            i = j + 1
        elif c == ".":
            parts.append(cur)
            cur = ""
            i += 1
        else:
            cur += c
            i += 1
    parts.append(cur)
    return [p for p in parts if p != ""]


def read_ident(s):
    """Leading identifier of s (after spaces), or ''."""
    s = s.lstrip()
    i = 0
    while i < len(s):
        c = s[i]
        if c == "«":
            j = s.find("»", i)
            if j < 0:
                break
            i = j + 1
        elif is_ident_char(c) or (c == "." and i > 0 and i + 1 < len(s) and (is_ident_char(s[i + 1]) or s[i + 1] == "«")):
            if i == 0 and (c.isdigit() or c in "'!?"):
                break
            i += 1
        else:
            break
    return s[:i]


class ScopeError(Exception):
    pass


class Analysis:
    """Scope events, declarations and closing commands of one Lean body."""

    def __init__(self, text, start=0):
        self.text = text
        self.masked, self.comments = mask(text)
        self.start = start
        self.decls = []      # (offset, fullname, private, kw)
        self.notations = []  # (offset, namespace, kw, mods, rest)
        self.global_effects = collections.Counter()
        self.closing = []    # commands closing scopes left open at the end
        self.indented = [m.start() for m in _INDENTED_SCOPE.finditer(self.masked, start)]
        self.exit_cmds = [m.start() for m in _EXIT.finditer(self.masked, start)]
        self.errors = []
        self._run()

    def line_of(self, off):
        return self.text.count("\n", 0, off) + 1

    def decl_text(self, off):
        """Normalized text from a declaration to the next scope/declaration/notation command."""
        nxt = min([o for o in self.event_offsets if o > off] + [len(self.text)])
        return " ".join(self.masked[off:nxt].split()) + "|" + " ".join(
            re.sub(r"--[^\n]*|/-.*?-/", " ", self.text[off:nxt], flags=re.S).split())

    def _run(self):
        events = []
        for m in _SCOPE.finditer(self.masked, self.start):
            events.append((m.start(), "scope", m))
        for m in _DECL.finditer(self.masked, self.start):
            events.append((m.start(), "decl", m))
        for m in _NOTATION.finditer(self.masked, self.start):
            events.append((m.start("kw"), "notation", m))
        events.sort(key=lambda e: e[0])
        self.event_offsets = [e[0] for e in events]
        stack = []  # [kind, component, cmd_id, full_name_of_cmd]
        for cmd_id, (off, typ, m) in enumerate(events):
            ns = ".".join(c for k, c, _, _ in stack if k == "ns")
            if typ == "scope":
                kw, name = m.group(2), m.group(3)
                if name.startswith("--") or name.startswith("/-"):
                    name = ""
                if kw == "namespace":
                    comps = split_name(name)
                    if not comps:
                        self.errors.append(f"line {self.line_of(off)}: namespace without a name")
                        continue
                    for c in comps:
                        stack.append(["ns", c, cmd_id, name])
                elif kw == "section":
                    comps = split_name(name) if name else [""]
                    for c in comps:
                        stack.append(["sec", c, cmd_id, name])
                elif kw == "mutual":
                    stack.append(["mutual", "", cmd_id, ""])
                else:  # end
                    if stack and stack[-1][0] == "mutual":
                        if name:
                            self.errors.append(f"line {self.line_of(off)}: `end {name}` closes a mutual block")
                        stack.pop()
                        continue
                    comps = split_name(name) if name else [""]
                    if len(comps) > len(stack):
                        self.errors.append(f"line {self.line_of(off)}: `end {name}` closes more scopes than are open")
                        stack.clear()
                        continue
                    top = stack[len(stack) - len(comps):]
                    if [c for _, c, _, _ in top] != comps:
                        self.errors.append(f"line {self.line_of(off)}: `end {name}` does not match open scopes "
                                           f"{[c for _, c, _, _ in top]}")
                    del stack[len(stack) - len(comps):]
            elif typ == "decl":
                mods, kw, rest = m.group("mods").split(), m.group("kw"), m.group("rest")
                kw = kw.split()[-1]
                if kw == "instance":
                    r = rest.lstrip()
                    if r.startswith("("):
                        depth, j = 0, 0
                        for j, c in enumerate(r):
                            depth += c == "("
                            depth -= c == ")"
                            if depth == 0:
                                break
                        r = r[j + 1:]
                    name = read_ident(r)
                else:
                    name = read_ident(rest)
                if name and name not in ("where", "extends", "deriving"):
                    full = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
                    self.decls.append((off, full, "private" in mods, kw))
                eff = self._effects_of_decl(m)
                for e in eff:
                    self.global_effects[e] += 1
            else:
                mods = m.group("mods").split()
                kw = m.group("kw")
                self.notations.append((off, ns, kw, tuple(mods), self.text[m.start("rest"):m.end("rest")].strip()))
                if "local" not in mods and "scoped" not in mods:
                    self.global_effects["syntax/macro"] += 1
        for m in _GLOBAL_ATTR.finditer(self.masked, self.start):
            attrs = m.group("attrs")
            if not re.match(r"\s*(local|scoped)\b", attrs):
                for a in re.split(r",", attrs):
                    a = a.strip()
                    if a.startswith("-"):
                        self.global_effects["attribute erase"] += 1
                    elif a.split(" ")[0] in ("simp", "instance", "reducible", "irreducible", "ext", "coe",
                                             "default_instance", "grind", "match_pattern", "semireducible"):
                        self.global_effects[f"attribute {a.split(' ')[0]}"] += 1
        if any(k == "mutual" for k, _, _, _ in stack):
            self.errors.append("body ends inside a mutual block")
        # closing commands, innermost first; one `end` per original command
        while stack:
            cid = stack[-1][2]
            group = []
            while stack and stack[-1][2] == cid:
                group.insert(0, stack.pop())
            kind = group[0][0]
            comps = [c for _, c, _, _ in group]
            if kind == "mutual":
                self.closing.append("end")
            elif kind == "sec" and comps == [""]:
                self.closing.append("end")
            else:
                self.closing.append("end " + ".".join(comps))

    def _effects_of_decl(self, m):
        mods = m.group("mods").split()
        kw = m.group("kw").split()[-1]
        line_start = self.masked.rfind("\n", 0, m.start()) + 1
        line = self.masked[line_start:m.end()]
        eff = []
        if kw == "instance" and "local" not in mods and "scoped" not in mods:
            eff.append("instance")
        attr = re.match(r"[ \t]*@\[([^\n]*?)\]", line)
        if attr:
            for a in attr.group(1).split(","):
                a = a.strip().split(" ")[0]
                if a in ("simp", "instance", "ext", "coe", "default_instance", "grind", "reducible", "match_pattern"):
                    eff.append(f"@[{a}]")
        return eff


# ======================================================================= repository

def git_lean_files(root):
    out = subprocess.run(["git", "-C", root, "ls-files", "-c", "-o", "--exclude-standard", "-z", "--", "*.lean"],
                         check=True, capture_output=True).stdout.decode()
    return sorted({p for p in out.split("\0") if p and os.path.exists(os.path.join(root, p))})


def path_to_module(p):
    return p[:-5].replace("/", ".")


def module_to_path(m):
    return m.replace(".", "/") + ".lean"


def in_area(path, area):
    if area is None:
        return False
    area = area.rstrip("/")
    if area.endswith(".lean"):
        area = area[:-5]
    return path == area + ".lean" or path.startswith(area + "/")


def is_shim_text(text):
    if SHIM_MARKER not in text:
        return None
    masked, _ = mask(text)
    h = parse_header(text)
    if len(h.imports) != 1 or masked[h.end:].strip():
        return None
    return h.imports[0][0]


class Repo:
    def __init__(self, root, moves_path=None):
        self.root = os.path.abspath(root)
        if not os.path.exists(os.path.join(self.root, "lakefile.lean")):
            sys.exit(f"{self.root}: no lakefile.lean (run from the repository root or pass --root)")
        self.moves_path = moves_path or os.path.join(self.root, ".refactor", "moves.tsv")
        self.paths = {}
        for p in git_lean_files(self.root):
            if p != "lakefile.lean":
                self.paths[path_to_module(p)] = p
        self._text = {}
        self.imports = {}
        self.lines = {}
        self.shims = {}
        for m, p in self.paths.items():
            t = self.text(m)
            h = parse_header(t)
            self.imports[m] = [x[0] for x in h.imports]
            self.lines[m] = t.count("\n")
            if SHIM_MARKER in t:
                tgt = is_shim_text(t)
                if tgt:
                    self.shims[m] = tgt
        self.importers = collections.defaultdict(set)
        for m, ims in self.imports.items():
            for i in ims:
                self.importers[i].add(m)
        self.moves = self.load_moves()
        self.exe_roots, self.lib_roots = self.lake_roots()

    def text(self, m):
        if m not in self._text:
            with open(os.path.join(self.root, self.paths[m]), encoding="utf-8") as f:
                self._text[m] = f.read()
        return self._text[m]

    def lake_roots(self):
        text = open(os.path.join(self.root, "lakefile.lean"), encoding="utf-8").read()
        exes = set(re.findall(r"root\s*:=\s*`([\w.«»]+)", text))
        libs = set(re.findall(r"lean_lib\s+«?([\w.]+)»?", text))
        self.lib_globs = re.findall(r"globs\s*:=\s*[^\n]*?`([\w.«»]+?)(\.\*|\.\+)?(?=[\s,\]\)]|$)", text)
        self.lib_globs += [(l, "") for l in libs]
        return exes, libs

    def built_by_lib(self, m):
        for base, kind in self.lib_globs:
            if (kind in ("", ".*") and m == base) or (kind in (".*", ".+") and m.startswith(base + ".")):
                return True
        return False

    def load_moves(self):
        """All recorded moves: every <root>/.refactor/moves*.tsv (sorted), then --moves.
        Later lines win for the same old module."""
        state = os.path.join(self.root, ".refactor")
        files = sorted(os.path.join(state, f) for f in os.listdir(state)
                       if f.startswith("moves") and f.endswith(".tsv")) if os.path.isdir(state) else []
        if os.path.abspath(self.moves_path) not in map(os.path.abspath, files) and os.path.exists(self.moves_path):
            files.append(self.moves_path)
        moves, origin = {}, {}
        for path in files:
            for l in open(path, encoding="utf-8"):
                parts = l.rstrip("\n").split("\t")
                if len(parts) >= 2 and not l.startswith("#"):
                    if parts[0] in moves and moves[parts[0]] != parts[1] and origin[parts[0]] != path:
                        print(f"warning: {parts[0]} moved to {moves[parts[0]]} in {origin[parts[0]]} and to "
                              f"{parts[1]} in {path}; using the latter", file=sys.stderr)
                    moves[parts[0]] = parts[1]
                    origin[parts[0]] = path
        return moves

    def append_moves(self, rows):
        os.makedirs(os.path.dirname(self.moves_path), exist_ok=True)
        new = not os.path.exists(self.moves_path)
        with open(self.moves_path, "a", encoding="utf-8") as f:
            if new:
                f.write("# old_module\tnew_module\tkind\n")
            for r in rows:
                f.write("\t".join(r) + "\n")

    def resolve(self, m, extra=None):
        """Final location of module m following moves (and pending `extra` moves)."""
        seen = set()
        while True:
            if m in seen:
                sys.exit(f"cycle in moves at {m}")
            seen.add(m)
            if extra and m in extra:
                m = extra[m]
                continue
            if m in self.paths and m not in self.shims:
                return m
            if m in self.moves:
                m = self.moves[m]
            elif m in self.shims:
                m = self.shims[m]
            else:
                return m

    def transitive_imports(self, m):
        seen, stack = set(), [m]
        while stack:
            x = stack.pop()
            for i in self.imports.get(x, []):
                if i not in seen:
                    seen.add(i)
                    stack.append(i)
        return seen

    def transitive_importers(self, m):
        seen, stack = set(), [m]
        while stack:
            x = stack.pop()
            for i in self.importers.get(x, ()):
                if i not in seen:
                    seen.add(i)
                    stack.append(i)
        return seen

    def write(self, m, text, dry):
        p = os.path.join(self.root, module_to_path(m))
        if dry:
            return
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            f.write(text)
        self._text[m] = text

    def delete(self, m, dry):
        if not dry:
            os.remove(os.path.join(self.root, self.paths[m]))


# ======================================================================= merge

def body_parts(text):
    """(pre-header comments, body) of a file."""
    h = parse_header(text)
    pre = text[:h.first_import].strip() if h.first_import else ""
    body = text[h.end:] if h.imports else text
    return pre, body


_PREAMBLE_LINE = re.compile(r"(set_option|open|namespace|noncomputable[ \t]+section|section|universe)\b")


def hoist_module_doc(body, a):
    """Move the first module doc to the front when only preamble commands precede it."""
    docs = [(s, e) for s, e, k in a.comments if k == "moddoc"]
    if not docs:
        return body
    s, e = docs[0]
    before = a.masked[:s]
    if not before.strip():
        return body
    for line in before.splitlines():
        if line.strip() and (not _PREAMBLE_LINE.match(line) or re.search(r"\bin\s*$", line)):
            return body
    rest = body[:s].rstrip() + "\n\n" + body[e:].lstrip("\n")
    return body[s:e] + "\n\n" + rest.lstrip("\n")


def wrap_body(module, text):
    """Section-wrapped body of a source file plus its Analysis."""
    pre, body = body_parts(text)
    body = body.strip("\n")
    a = Analysis(body)
    body = hoist_module_doc(body, a)
    content = (pre + "\n" if pre else "") + body
    lines = ["section", FROM_MARKER + module, content.rstrip()]
    lines += a.closing
    lines.append("end")
    return "\n".join(lines) + "\n", a


def topo_order(nodes, deps):
    """Stable Kahn: nodes in given order; deps[n] = set of nodes that must come first."""
    placed, order = set(), []
    remaining = list(nodes)
    while remaining:
        for n in remaining:
            if deps[n] <= placed:
                order.append(n)
                placed.add(n)
                remaining.remove(n)
                break
        else:
            raise SystemExit(f"cyclic imports among {remaining}")
    return order


def plan_merge(repo, target, area, sources, kind):
    errors, warnings = [], []
    if len(set(sources)) != len(sources):
        errors.append("a source is listed twice")
    if target in sources:
        errors.append("the target is also a source")
    for s in sources:
        if s not in repo.paths:
            errors.append(f"{s}: no such module")
        elif s in repo.shims:
            errors.append(f"{s}: is a refactor shim (merge its target instead)")
        elif s in repo.exe_roots or s in repo.lib_roots:
            errors.append(f"{s}: is a lakefile root")
    if errors:
        return None, errors, warnings
    target_exists = target in repo.paths and target not in repo.shims
    if target in repo.moves and not target_exists:
        errors.append(f"{target}: this name was moved away earlier ({target} -> {repo.moves[target]}); "
                      f"pick another target name or run consolidate first")
    if target in repo.shims:
        errors.append(f"{target}: is a refactor shim")
    if target in repo.exe_roots:
        errors.append(f"{target}: is a lean_exe root")
    if not repo.built_by_lib(target):
        warnings.append(f"{target} is not matched by any lean_lib glob/root; `lake build <lib>` will not build it")
    tpath = module_to_path(target)
    if area and not in_area(tpath, area):
        warnings.append(f"target {tpath} is outside --area {area}")
    # analyses
    texts = {s: repo.text(s) for s in sources}
    if target_exists:
        texts[target] = repo.text(target)
    analyses = {}
    for m, t in texts.items():
        h = parse_header(t)
        if h.module_system or h.modifiers:
            errors.append(f"{m}: uses the module system (`module` header or import modifiers)")
        if h.prelude:
            errors.append(f"{m}: has `prelude`")
        a = Analysis(t, start=h.end)
        analyses[m] = a
        for e in a.errors:
            errors.append(f"{m}: {e}")
        if a.indented:
            errors.append(f"{m}: scope command not at column 0 (line {a.line_of(a.indented[0])}); fix by hand first")
        if a.exit_cmds:
            errors.append(f"{m}: contains #exit")
    if errors:
        return None, errors, warnings
    # group and resolved imports
    pending = {s: target for s in sources}
    group = set(sources) | {target}
    merged_into_target = {m for m in set(repo.paths) | set(repo.moves) if repo.resolve(m, pending) == target}
    def resolved_imports(m):
        out = []
        for i in repo.imports.get(m, []):
            r = repo.resolve(i, pending)
            if r not in out:
                out.append(r)
        return out
    # import cycles: a path between group members through a module outside the group
    outside = set()
    for m in group & set(repo.paths):
        for i in resolved_imports(m):
            if i not in group and i not in merged_into_target:
                outside.add(i)
    seen, stack, hit = set(), list(outside), {}
    parent = {}
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        for i in repo.imports.get(x, []):
            r = repo.resolve(i, pending)
            if r in group or r in merged_into_target or i in group:
                hit.setdefault(x, i)
            elif r not in seen:
                parent.setdefault(r, x)
                stack.append(r)
    if hit:
        x, i = next(iter(sorted(hit.items())))
        chain = [x]
        while chain[-1] in parent:
            chain.append(parent[chain[-1]])
        errors.append(f"import cycle: {' <- '.join(reversed(chain))} imports {i} (in the group); "
                      f"{len(hit)} outside module(s) depend on the group")
    # body order: topological on direct imports inside the group
    nodes = ([target] if target_exists else []) + list(sources)
    deps = {n: set() for n in nodes}
    for n in nodes:
        for i in repo.imports.get(n, []):
            r0 = repo.resolve(i)
            if r0 in deps and r0 != n:
                deps[n].add(r0)
            elif i in deps and i != n:
                deps[n].add(i)
    try:
        order = topo_order(nodes, deps)
    except SystemExit as e:
        errors.append(str(e))
        order = nodes
    # declaration clashes between bodies (same full name declared twice)
    owner = {}
    for m in order:
        for off, full, priv, kw in analyses[m].decls:
            if full in owner and owner[full][0] != m:
                om, opriv, ooff = owner[full]
                same = analyses[om].decl_text(ooff) == analyses[m].decl_text(off)
                errors.append(f"name clash: {full} declared in {om}{' (private)' if opriv else ''} and "
                              f"{m}{' (private)' if priv else ''}"
                              + (f"; the two declarations are textually identical: keep the copy from {om} "
                                 f"(it comes first), delete the one in {m}, merge again; the snapshot diff "
                                 f"stays empty" if same else ""))
            else:
                owner.setdefault(full, (m, priv, off))
    # notation kinds that may collide (same namespace and same leading atom)
    nseen = {}
    for m in order:
        for off, ns, kw, mods, rest in analyses[m].notations:
            atom = re.match(r'\s*(?:\([^)]*\)\s*)*(?:\w+\s*)?(?::\w+\s*)?"([^"]*)"', rest)
            key = (ns, kw, atom.group(1) if atom else rest[:30])
            if key in nseen and nseen[key] != m:
                warnings.append(f"{m}: `{kw}` with leading atom {key[2]!r} in namespace {ns or '_root_'} also in "
                                f"{nseen[key]}; generated names may get a suffix (check the snapshot)")
            nseen.setdefault(key, m)
    # newly visible global effects
    closure = {m: repo.transitive_imports(m) for m in order}
    for k, m in enumerate(order):
        for p in order[:k]:
            if p == target:
                continue
            if p not in closure[m] and analyses[p].global_effects:
                eff = ", ".join(f"{c} {e}" for e, c in sorted(analyses[p].global_effects.items()))
                warnings.append(f"{m} did not import {p}, whose global effects ({eff}) now precede it")
    # imports of the merged file
    imports = []
    for n in order:
        for i in resolved_imports(n):
            if i not in group and i not in merged_into_target and i not in imports:
                imports.append(i)
    # importers to rewrite / shims
    rewrites, shims = collections.defaultdict(dict), []
    for s in sources:
        outside_importers = []
        for imp in sorted(repo.importers.get(s, ())):
            if imp in group:
                continue
            if in_area(repo.paths[imp], area):
                rewrites[imp][s] = target
            else:
                outside_importers.append(imp)
        if outside_importers:
            shims.append((s, outside_importers))
    plan = dict(target=target, target_exists=target_exists, order=order, imports=imports,
                rewrites=rewrites, shims=shims, analyses=analyses, kind=kind)
    return plan, errors, warnings


def render_merged(repo, plan):
    target = plan["target"]
    head = "".join(f"import {i}\n" for i in plan["imports"])
    parts = []
    for n in plan["order"]:
        t = repo.text(n)
        if n == target:
            pre, body = body_parts(t)
            body = body.strip("\n")
            if FROM_MARKER in body:
                parts.append((pre + "\n" if pre else "") + body + "\n")
            else:
                parts.append(wrap_body(n, t)[0])
        else:
            parts.append(wrap_body(n, t)[0])
    return head + "\n" + "\n".join(parts)


def execute(repo, plan, dry):
    target = plan["target"]
    text = render_merged(repo, plan)
    print(f"{'would write' if dry else 'wrote'} {module_to_path(target)} "
          f"({text.count(chr(10))} lines, bodies: {', '.join(plan['order'])})")
    repo.write(target, text, dry)
    for imp, mapping in sorted(plan["rewrites"].items()):
        t = repo.text(imp)
        new, changed = rewrite_imports(t, mapping, self_module=imp)
        if changed:
            repo.write(imp, new, dry)
            print(f"  rewrote imports of {repo.paths[imp]}")
    shim_of = dict(plan["shims"])
    srcs = [n for n in plan["order"] if n != target]
    for s in srcs:
        if s in shim_of:
            ims = shim_of[s]
            repo.write(s, f"import {target}\n{SHIM_MARKER}\n", dry)
            print(f"  shim {repo.paths[s]} (imported outside the area by {len(ims)}: "
                  f"{', '.join(ims[:3])}{' ...' if len(ims) > 3 else ''})")
        else:
            repo.delete(s, dry)
            print(f"  deleted {repo.paths[s]}")
    if not dry:
        repo.append_moves([(s, target, plan["kind"]) for s in srcs])


def cmd_merge(args):
    repo = Repo(args.root, args.moves)
    plan, errors, warnings = plan_merge(repo, args.into, args.area, args.sources, "merge")
    for w in warnings:
        print("warning:", w, file=sys.stderr)
    if errors:
        for e in errors:
            print("refused:", e, file=sys.stderr)
        sys.exit(1)
    execute(repo, plan, args.dry_run)


def cmd_move(args):
    repo = Repo(args.root, args.moves)
    old, new = args.old, args.new
    if new in repo.paths and new not in repo.shims:
        sys.exit(f"refused: {new} exists (use merge)")
    if new in repo.shims:
        sys.exit(f"refused: {new} is a shim")
    plan, errors, warnings = plan_merge(repo, new, args.area, [old], "move")
    for w in warnings:
        if "did not import" not in w:
            print("warning:", w, file=sys.stderr)
    if errors:
        for e in errors:
            print("refused:", e, file=sys.stderr)
        sys.exit(1)
    # a move keeps the file verbatim apart from resolved imports
    t = repo.text(old)
    mapping = {i: repo.resolve(i, {old: new}) for i in repo.imports[old]}
    text, _ = rewrite_imports(t, mapping, self_module=new)
    print(f"{'would move' if args.dry_run else 'moved'} {repo.paths[old]} -> {module_to_path(new)}")
    repo.write(new, text, args.dry_run)
    for imp, mp in sorted(plan["rewrites"].items()):
        nt, changed = rewrite_imports(repo.text(imp), mp, self_module=imp)
        if changed:
            repo.write(imp, nt, args.dry_run)
            print(f"  rewrote imports of {repo.paths[imp]}")
    if plan["shims"]:
        ims = plan["shims"][0][1]
        repo.write(old, f"import {new}\n{SHIM_MARKER}\n", args.dry_run)
        print(f"  shim {repo.paths[old]} (imported outside the area by {len(ims)}: {', '.join(ims[:3])}"
              f"{' ...' if len(ims) > 3 else ''})")
    else:
        repo.delete(old, args.dry_run)
        print(f"  deleted {repo.paths[old]}")
    if not args.dry_run:
        repo.append_moves([(old, new, "move")])


# ======================================================================= consolidate

def cmd_consolidate(args):
    repo = Repo(args.root, args.moves)
    dry = args.dry_run
    final = {}
    for m in set(repo.moves) | set(repo.shims):
        f = repo.resolve(m)
        if f != m:
            final[m] = f
    for m, f in sorted(final.items()):
        if f not in repo.paths or f in repo.shims:
            sys.exit(f"refused: {m} resolves to {f}, which is not a module file")
    n_files = 0
    for m in sorted(repo.paths):
        if m in repo.shims:
            continue
        mapping = {i: final[i] for i in repo.imports[m] if i in final}
        if not mapping:
            continue
        new, changed = rewrite_imports(repo.text(m), mapping, self_module=m)
        if changed:
            n_files += 1
            repo.write(m, new, dry)
    print(f"{'would rewrite' if dry else 'rewrote'} imports in {n_files} files")
    for m in sorted(repo.shims):
        print(f"{'would delete' if dry else 'deleted'} shim {repo.paths[m]} (-> {final.get(m, repo.shims[m])})")
        repo.delete(m, dry)
    # text references in docs and scripts
    exts = tuple("." + e.strip(".") for e in args.ext.split(","))
    out = subprocess.run(["git", "-C", repo.root, "ls-files", "-c", "-o", "--exclude-standard", "-z"],
                         check=True, capture_output=True).stdout.decode()
    files = [p for p in out.split("\0") if p.endswith(exts) and os.path.exists(os.path.join(repo.root, p))]
    pats = []
    for m, f in sorted(final.items(), key=lambda kv: -len(kv[0])):
        old_p, new_p = module_to_path(m), module_to_path(f)
        pats.append((re.compile(r"(?<![\w.-])" + re.escape(old_p) + r"(?![\w])"), new_p, old_p))
        pats.append((re.compile(r"(?<![\w.])" + re.escape(m) + r"(?![\w'!?])(?!\.[\w«])"), f, m))
    anchor_warn = []
    for p in files:
        full = os.path.join(repo.root, p)
        try:
            t = open(full, encoding="utf-8").read()
        except UnicodeDecodeError:
            continue
        t0, count = t, 0
        for rx, new, old in pats:
            if old.endswith(".lean"):
                for mm in re.finditer(re.escape(old) + r"(?::\d+|#L\d+)", t):
                    anchor_warn.append(f"{p}: {mm.group()} (line anchor now stale)")
            t, k = rx.subn(new, t)
            count += k
        if t != t0:
            print(f"{'would update' if dry else 'updated'} {count} reference(s) in {p}")
            if not dry:
                with open(full, "w", encoding="utf-8") as f:
                    f.write(t)
    for w in anchor_warn:
        print("warning:", w, file=sys.stderr)


# ======================================================================= graph and analyses

def cmd_graph(args):
    repo = Repo(args.root, args.moves)
    mods = sorted(repo.paths)
    if args.area:
        mods = [m for m in mods if in_area(repo.paths[m], args.area)]
    if args.importers or args.imports:
        m = args.importers or args.imports
        if args.importers:
            xs = sorted(repo.transitive_importers(m)) if args.transitive else sorted(repo.importers.get(m, ()))
        else:
            xs = sorted(repo.transitive_imports(m)) if args.transitive else repo.imports.get(m, [])
        for x in xs:
            tag = ""
            if args.area and x in repo.paths:
                tag = "  [in area]" if in_area(repo.paths[x], args.area) else "  [outside area]"
            print(x + tag)
        print(f"# {len(xs)} {'transitive ' if args.transitive else ''}{'importers' if args.importers else 'imports'}"
              f" of {m}", file=sys.stderr)
        return
    if args.chains or args.siblings:
        return candidates(repo, mods, args)
    print(f"modules: {len(mods)}, lines: {sum(repo.lines[m] for m in mods)}, shims: {len(repo.shims)}, "
          f"recorded moves: {len(repo.moves)}")
    buckets = [0, 1, 2, 3, 5, 10, 20, 50, 100, 1000, 10 ** 9]
    def hist(values, label):
        c = collections.Counter()
        for v in values:
            for lo, hi in zip(buckets, buckets[1:]):
                if lo <= v < hi:
                    c[(lo, hi)] += 1
                    break
        print(label)
        for (lo, hi), k in sorted(c.items()):
            print(f"  {lo:>5}-{hi - 1 if hi < 10 ** 9 else '':<6} {k}")
    hist([len(repo.importers.get(m, ())) for m in mods], "importers per module:")
    lb = [0, 25, 50, 100, 200, 400, 800, 1600, 3200, 10 ** 9]
    c = collections.Counter()
    for m in mods:
        for lo, hi in zip(lb, lb[1:]):
            if lo <= repo.lines[m] < hi:
                c[(lo, hi)] += 1
    print("lines per module:")
    for (lo, hi), k in sorted(c.items()):
        print(f"  {lo:>5}-{hi - 1 if hi < 10 ** 9 else '':<6} {k}")
    top = sorted(mods, key=lambda m: -len(repo.importers.get(m, ())))[:args.top]
    print(f"most imported:")
    for m in top:
        print(f"  {len(repo.importers.get(m, ())):6}  {m}")
    dirs = collections.Counter(os.path.dirname(repo.paths[m]) for m in mods)
    print("modules per directory:")
    for d, k in dirs.most_common(args.top):
        print(f"  {k:6}  {d}")


def candidates(repo, mods, args):
    modset = set(mods)
    if args.chains:
        # chains: a module whose only importer (besides umbrella files) is in the same directory
        umbrellas = {m for m in repo.paths if len(repo.imports.get(m, [])) > 50 and repo.lines[m] <= len(repo.imports[m]) + 20}
        sole = {}
        for m in mods:
            ims = [i for i in repo.importers.get(m, ()) if i not in umbrellas]
            if len(ims) == 1 and ims[0] in modset and os.path.dirname(repo.paths[ims[0]]) == os.path.dirname(repo.paths[m]):
                sole[m] = ims[0]
        heads = set(sole.values()) - set(sole)
        groups = []
        for h in heads:
            members, stack = [h], [h]
            while stack:
                x = stack.pop()
                for y, p in sole.items():
                    if p == x:
                        members.append(y)
                        stack.append(y)
            if len(members) >= args.min_group:
                total = sum(repo.lines[x] for x in members)
                if total <= args.max_lines:
                    groups.append((total, members))
        for total, members in sorted(groups, key=lambda g: (-len(g[1]), g[0]))[:args.top]:
            outside = set()
            for x in members:
                outside |= {i for i in repo.importers.get(x, ()) if i not in members}
            print(f"chain of {len(members)} ({total} lines; importers outside the chain: {len(outside)}): "
                  + " ".join(members))
    if args.siblings:
        by_key = collections.defaultdict(list)
        for m in mods:
            key = (os.path.dirname(repo.paths[m]), frozenset(repo.importers.get(m, ())))
            if key[1]:
                by_key[key].append(m)
        groups = [(sum(repo.lines[x] for x in v), v, k) for k, v in by_key.items() if len(v) >= args.min_group]
        for total, members, key in sorted(groups, key=lambda g: (-len(g[1]), g[0]))[:args.top]:
            ms = sorted(members)
            print(f"siblings x{len(members)} ({total} lines) sharing {len(key[1])} importer(s) "
                  f"[{', '.join(sorted(key[1])[:2])}{' ...' if len(key[1]) > 2 else ''}]: " + " ".join(ms[:12])
                  + (f" ... ({len(ms) - 12} more)" if len(ms) > 12 else ""))


def cmd_clashes(args):
    """Estimate private clashes: duplicate declared names among files of the same directory."""
    repo = Repo(args.root, args.moves)
    mods = sorted(m for m in repo.paths if (not args.area or in_area(repo.paths[m], args.area)))
    decls = {}
    for m in mods:
        t = repo.text(m)
        h = parse_header(t)
        decls[m] = Analysis(t, start=h.end).decls
    by_dir = collections.defaultdict(list)
    for m in mods:
        by_dir[os.path.dirname(repo.paths[m])].append(m)
    n_private = sum(1 for m in mods for d in decls[m] if d[2])
    print(f"files: {len(mods)}, private declarations found: {n_private}")
    tot_names = tot_pub = 0
    all_files, all_pairs = set(), set()
    rows, top = [], []
    for d, ms in sorted(by_dir.items()):
        owner = collections.defaultdict(list)
        for m in ms:
            for off, full, priv, kw in decls[m]:
                owner[full].append((m, priv))
        files, pairs, names = set(), set(), 0
        for full, lst in owner.items():
            fs = sorted({m for m, _ in lst})
            if len(fs) < 2:
                continue
            if not any(p for _, p in lst):
                tot_pub += 1
                continue
            names += 1
            files |= set(fs)
            for i in range(len(fs)):
                for j in range(i + 1, len(fs)):
                    pairs.add((fs[i], fs[j]))
            top.append((len(fs), full, fs))
        tot_names += names
        all_files |= files
        all_pairs |= pairs
        if names:
            rows.append((d, len(ms), names, len(files), len(pairs)))
    print(f"same-directory duplicate names involving a private declaration: {tot_names} names, "
          f"{len(all_files)} files ({100.0 * len(all_files) / max(1, len(mods)):.1f}% of files), {len(all_pairs)} file pairs")
    print(f"same-directory duplicate names, all public: {tot_pub}")
    print("per directory: files, clashing names, files involved, file pairs")
    for d, n, names, f, p in sorted(rows, key=lambda r: -r[3]):
        print(f"  {d}: {n} files, {names} names, {f} files ({100.0 * f / n:.1f}%), {p} pairs")
    print("names shared by most files:")
    for k, full, fs in sorted(top, key=lambda t: -t[0])[:args.top]:
        print(f"  {k:4} files  {full}  ({', '.join(fs[:3])}{' ...' if len(fs) > 3 else ''})")


def cmd_scan(args):
    for f in args.files:
        t = open(f, encoding="utf-8").read()
        h = parse_header(t)
        a = Analysis(t, start=h.end)
        print(f"== {f}: {len(h.imports)} imports, header ends at {h.end}, module_system={h.module_system}")
        for e in a.errors:
            print("  error:", e)
        for off, full, priv, kw in a.decls:
            print(f"  decl {kw} {full}{' (private)' if priv else ''}  line {a.line_of(off)}")
        print("  closing:", a.closing)
        print("  global effects:", dict(a.global_effects))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--moves", help="moves file (default <root>/.refactor/moves.tsv)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("graph")
    g.add_argument("--importers")
    g.add_argument("--imports")
    g.add_argument("--transitive", action="store_true")
    g.add_argument("--area")
    g.add_argument("--top", type=int, default=15)
    g.add_argument("--chains", action="store_true", help="sole-importer chains inside a directory")
    g.add_argument("--siblings", action="store_true", help="modules of a directory with identical importers")
    g.add_argument("--min-group", type=int, default=3)
    g.add_argument("--max-lines", type=int, default=3000)
    m = sub.add_parser("merge")
    m.add_argument("--into", required=True)
    m.add_argument("--area", required=True)
    m.add_argument("--dry-run", action="store_true")
    m.add_argument("sources", nargs="+")
    mv = sub.add_parser("move")
    mv.add_argument("old")
    mv.add_argument("new")
    mv.add_argument("--area", required=True)
    mv.add_argument("--dry-run", action="store_true")
    c = sub.add_parser("consolidate")
    c.add_argument("--dry-run", action="store_true")
    c.add_argument("--ext", default="md,py,mjs")
    cl = sub.add_parser("clashes")
    cl.add_argument("--area")
    cl.add_argument("--top", type=int, default=10)
    s = sub.add_parser("scan")
    s.add_argument("files", nargs="+")
    args = ap.parse_args()
    {"graph": cmd_graph, "merge": cmd_merge, "move": cmd_move, "consolidate": cmd_consolidate,
     "clashes": cmd_clashes, "scan": cmd_scan}[args.cmd](args)


if __name__ == "__main__":
    main()
