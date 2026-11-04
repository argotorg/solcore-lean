#!/usr/bin/env python3
"""Declaration snapshots for pure-refactor verification.

  snapshot.py take OUT.jsonl [--root DIR] [--modules FILE] [--threads N] [--jobs J] [--no-check]
  snapshot.py diff A.jsonl B.jsonl [--renames renames.tsv] [--limit N]

`take` runs DeclSnapshot.lean (next to this script) with `lake env lean --run` from the
worktree root and writes one JSON line per constant, sorted:

  {"f": [flags], "k": kind, "m": module, "n": normalized name, "t": type hash, "v": value hash}

`v` is absent for theorems. `m` is informational; `diff` ignores it. Constants skipped by
design are listed in OUT.skipped.tsv, and OUT.meta.json records what was snapshotted.

Default module set: every `*.lean` file known to git (tracked, or untracked and not ignored)
except lakefile.lean, files whose header is `module` (Lean module system), and files that
no Lake target builds (scripts run with `lean --run`). `lean_exe` roots each define `main`,
so each is imported in its own process; all other modules are imported together.

Before snapshotting, `lake build --no-build` checks that every olean is up to date; a stale
olean would make the snapshot meaningless (and a deleted module's old olean would conflict).

`diff` compares, per normalized name, the set of records (kind, type, value, flags); several
modules can define same-named privates, and identical records collapse. Exit status is 1
when anything was added, removed or changed. A renames file has lines `old<TAB>new` (exact
names) or `old.*<TAB>new.*` (prefix); a rename moves only those records of A's `old` that B
has under `new`. An exact `old` can have several lines, one for each differing copy of a
private helper that got a name of its own.
"""
import argparse, json, os, re, subprocess, sys, time, collections, concurrent.futures

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_PROG = os.path.join(HERE, "DeclSnapshot.lean")

# ---------------------------------------------------------------- module discovery

def strip_comments_head(text):
    """Return text after leading whitespace and comments (nested block comments)."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith("/--", i) and not text.startswith("/-!", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1; i += 2
                elif text.startswith("-/", i):
                    depth -= 1; i += 2
                else:
                    i += 1
        else:
            break
    return text[i:]


def is_module_system_file(path):
    with open(path, encoding="utf-8") as f:
        head = strip_comments_head(f.read(20000))
    return re.match(r"(prelude\s+)?module\b", head) is not None


def git_lean_files(root):
    out = subprocess.run(["git", "-C", root, "ls-files", "-c", "-o", "--exclude-standard", "-z", "--", "*.lean"],
                         check=True, capture_output=True).stdout.decode()
    files = sorted({p for p in out.split("\0") if p and os.path.exists(os.path.join(root, p))})
    return files


def path_to_module(p):
    return p[:-5].replace("/", ".")


IMPORT_RE = re.compile(r"^import\s+(.+)$")


def header_imports(path):
    """Imports in the file header (stops at the first non-import command)."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    mods = []
    rest = strip_comments_head(text)
    while True:
        m = re.match(r"(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([^\n]*)", rest)
        if not m:
            break
        line = m.group(1).split("--")[0]
        mods += [t for t in line.split() if t]
        rest = strip_comments_head(rest[m.end():])
    return mods


def parse_lakefile(root):
    """Very small parser for lean_lib globs/roots and lean_exe roots in lakefile.lean."""
    path = os.path.join(root, "lakefile.lean")
    text = open(path, encoding="utf-8").read()
    libs, exes = [], []
    blocks = re.split(r"\n(?=(?:@\[[^\]]*\]\s*)?(?:lean_lib|lean_exe|package|require|target|input_file|input_dir)\b)", text)
    for b in blocks:
        b2 = re.sub(r"^@\[[^\]]*\]\s*", "", b.strip())
        m = re.match(r"lean_lib\s+(\S+)", b2)
        if m:
            name = m.group(1).strip("«»")
            globs = re.findall(r"`([\w.«»]+?)(\.\*|\.\+)?(?=[\s,\]\)]|$)", (re.search(r"globs\s*:=\s*(.*)", b2) or [None, ""])[1] or "")
            roots = re.findall(r"`([\w.«»]+)", (re.search(r"roots\s*:=\s*(.*)", b2) or [None, ""])[1] or "")
            if not globs:
                globs = [(r, "") for r in (roots or [name])]
            libs.append((name, globs))
            continue
        m = re.match(r"lean_exe\s+(\S+)", b2)
        if m:
            name = m.group(1).strip("«»")
            r = re.search(r"root\s*:=\s*`([\w.«»]+)", b2)
            exes.append(r.group(1) if r else name)
    return libs, exes


def discover(root):
    files = git_lean_files(root)
    files = [f for f in files if f != "lakefile.lean"]
    mod_of = {f: path_to_module(f) for f in files}
    modset = set(mod_of.values())
    libs, exes = parse_lakefile(root)
    targets = set()
    for _, globs in libs:
        for base, kind in globs:
            for m in modset:
                if kind == ".*" and (m == base or m.startswith(base + ".")):
                    targets.add(m)
                elif kind == ".+" and m.startswith(base + "."):
                    targets.add(m)
                elif kind == "" and m == base:
                    targets.add(m)
    targets |= {e for e in exes if e in modset}
    imports = {mod_of[f]: header_imports(os.path.join(root, f)) for f in files}
    built, stack = set(), list(targets)
    while stack:
        m = stack.pop()
        if m in built or m not in modset:
            continue
        built.add(m)
        stack += [i for i in imports.get(m, []) if i in modset]
    modsys = sorted(mod_of[f] for f in files if is_module_system_file(os.path.join(root, f)))
    unbuilt = sorted(modset - built)
    chosen = sorted(built - set(modsys))
    return chosen, sorted(e for e in exes if e in built), modsys, unbuilt


# ---------------------------------------------------------------- take

def run(cmd, cwd, log=None):
    t0 = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if log is not None:
        log.append({"cmd": " ".join(cmd[:6]) + (" ..." if len(cmd) > 6 else ""), "secs": round(time.time() - t0, 1),
                    "rc": p.returncode})
    return p


def max_rss_of(stderr):
    m = re.search(r"(\d+)\s+maximum resident set size", stderr)
    return int(m.group(1)) if m else None


def take(args):
    root = os.path.abspath(args.root)
    out = os.path.abspath(args.out)
    t_start = time.time()
    if args.modules:
        mods = [l.strip() for l in open(args.modules) if l.strip() and not l.startswith("#")]
        _, exes, modsys, unbuilt = discover(root)
        exes = [e for e in exes if e in mods]
    else:
        mods, exes, modsys, unbuilt = discover(root)
    print(f"modules: {len(mods)} ({len(exes)} lean_exe roots imported separately); "
          f"skipped {len(modsys)} module-system files, {len(unbuilt)} files no target builds", file=sys.stderr)
    log = []
    if not args.no_check:
        libs, _ = parse_lakefile(root)
        check_targets = [name for name, _ in libs] + exes
        p = run(["lake", "build", "--no-build"] + check_targets, root, log)
        if p.returncode != 0:
            tail = "\n".join((p.stdout + p.stderr).strip().splitlines()[-15:])
            sys.exit(f"stale or missing build outputs; run `lake build {' '.join(check_targets)}` first:\n{tail}")
    tmpdir = out + ".parts"
    os.makedirs(tmpdir, exist_ok=True)
    exeset = set(exes)
    groups = [[m for m in mods if m not in exeset]] + [[e] for e in exes]
    jobs = []
    for i, g in enumerate(groups):
        if not g:
            continue
        gf = os.path.join(tmpdir, f"group{i}.txt")
        with open(gf, "w") as f:
            f.write("\n".join(g) + "\n")
        jobs.append((i, gf, os.path.join(tmpdir, f"group{i}.jsonl"), args.threads if i == 0 else 1))

    def one(job):
        i, gf, gout, threads = job
        cmd = ["/usr/bin/time", "-l", "lake", "env", "lean", "--run", LEAN_PROG, gf, gout, str(threads)]
        t0 = time.time()
        p = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
        return i, p, time.time() - t0, gout

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        for i, p, secs, gout in ex.map(one, jobs):
            info = [l for l in p.stderr.splitlines() if l.startswith(("group", "total"))]
            results.append({"group": i, "secs": round(secs, 1), "max_rss": max_rss_of(p.stderr), "info": info})
            if p.returncode != 0:
                sys.exit(f"DeclSnapshot failed for group {i}:\n{p.stdout}\n{p.stderr[-4000:]}")
    lines, skipped = set(), set()
    for _, _, gout, _ in jobs:
        with open(gout, encoding="utf-8") as f:
            lines.update(l.rstrip("\n") for l in f if l.strip())
        with open(gout + ".skipped.tsv", encoding="utf-8") as f:
            skipped.update(l.rstrip("\n") for l in f if l.strip())
    recs = sorted(lines, key=lambda l: (json.loads(l)["n"], l))
    with open(out, "w", encoding="utf-8") as f:
        for l in recs:
            f.write(l + "\n")
    with open(out + ".skipped.tsv", "w", encoding="utf-8") as f:
        for l in sorted(skipped):
            f.write(l + "\n")
    head = subprocess.run(["git", "-C", root, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    status = subprocess.run(["git", "-C", root, "status", "--porcelain"], capture_output=True, text=True).stdout
    meta = {"root": root, "head": head, "dirty_files": len(status.splitlines()), "modules": len(mods),
            "exe_roots": exes, "module_system_files": modsys, "unbuilt_files": unbuilt,
            "constants": len(recs), "skipped": len(skipped), "wall_secs": round(time.time() - t_start, 1),
            "groups": results, "checks": log}
    with open(out + ".meta.json", "w") as f:
        json.dump(meta, f, indent=1)
    for p in jobs:
        for suffix in ("", ".skipped.tsv"):
            try:
                os.remove(p[2] + suffix)
            except FileNotFoundError:
                pass
        os.remove(p[1])
    os.rmdir(tmpdir)
    rss = max((r["max_rss"] or 0) for r in results)
    print(f"wrote {len(recs)} constants ({len(skipped)} skipped) to {out} in {meta['wall_secs']} s; "
          f"largest process max RSS {rss / 2**30:.1f} GiB", file=sys.stderr)


# ---------------------------------------------------------------- diff

def load(path):
    recs = collections.defaultdict(set)
    mods = collections.defaultdict(set)
    with open(path, encoding="utf-8") as f:
        for l in f:
            if not l.strip():
                continue
            d = json.loads(l)
            recs[d["n"]].add((d["k"], d["t"], d.get("v"), tuple(d.get("f", []))))
            mods[d["n"]].add(d.get("m"))
    return recs, mods


def load_renames(path):
    exact, prefix = collections.defaultdict(list), []
    for l in open(path, encoding="utf-8"):
        l = l.rstrip("\n")
        if not l.strip() or l.startswith("#"):
            continue
        a, b = l.split("\t")[:2]
        if a.endswith(".*") and b.endswith(".*"):
            prefix.append((a[:-1], b[:-1]))
        else:
            exact[a].append(b)
    return exact, prefix


def rename(n, exact, prefix):
    if n in exact:
        return exact[n]
    for a, b in prefix:
        if n.startswith(a):
            return [b + n[len(a):]]
    return []


def describe(rs):
    out = []
    for k, t, v, f in sorted(rs, key=str):
        out.append(f"{k} t={t}" + (f" v={v}" if v else "") + (f" f={','.join(f)}" if f else ""))
    return "; ".join(out)


def diff(args):
    a, am = load(args.a)
    b, bm = load(args.b)
    if args.renames:
        # A rename moves only the records of `old` that appear under `new` in B, so a private
        # helper renamed in one module does not drag along same-named privates of other modules.
        exact, prefix = load_renames(args.renames)
        a2, am2 = collections.defaultdict(set), collections.defaultdict(set)
        for n, rs in a.items():
            moved = set()
            for new in rename(n, exact, prefix):
                here = {r for r in rs if r in b.get(new, ())}
                if here:
                    a2[new] |= here
                    am2[new] |= am[n]
                    moved |= here
            # identical records collapse: a record B still has under `old` stays there as well
            stay = (rs - moved) | (rs & b.get(n, set()))
            if stay:
                a2[n] |= stay
                am2[n] |= am[n]
        a, am = a2, am2
    removed = sorted(set(a) - set(b))
    added = sorted(set(b) - set(a))
    changed = sorted(n for n in set(a) & set(b) if a[n] != b[n])
    moved = sum(1 for n in set(a) & set(b) if am[n] != bm[n])
    lim = args.limit
    for title, names in (("removed", removed), ("added", added)):
        if names:
            print(f"== {title}: {len(names)}")
            for n in names[:lim]:
                rs = a[n] if title == "removed" else b[n]
                print(f"  {n}  [{describe(rs)}]  ({', '.join(sorted(map(str, (am if title == 'removed' else bm)[n])))})")
            if len(names) > lim:
                print(f"  ... {len(names) - lim} more")
    if changed:
        print(f"== changed: {len(changed)}")
        for n in changed[:lim]:
            fields = []
            ra, rb = a[n] - b[n], b[n] - a[n]
            if len(ra) == 1 and len(rb) == 1:
                (ka, ta, va, fa), = ra
                (kb, tb, vb, fb), = rb
                if ka != kb: fields.append(f"kind {ka}->{kb}")
                if ta != tb: fields.append("type")
                if va != vb: fields.append("value")
                if fa != fb: fields.append(f"flags {list(fa)}->{list(fb)}")
            else:
                fields.append(f"{len(ra)} record(s) only in A, {len(rb)} only in B")
            shared = len(a[n] & b[n])
            print(f"  {n}: {', '.join(fields)}" + (f" ({shared} identical record(s) of same-named "
                                                   f"declarations elsewhere)" if shared else "")
                  + f"\n    A: {describe(ra)}\n    B: {describe(rb)}")
        if len(changed) > lim:
            print(f"  ... {len(changed) - lim} more")
    total = len(removed) + len(added) + len(changed)
    print(f"summary: {len(a)} names in A, {len(b)} in B; removed {len(removed)}, added {len(added)}, "
          f"changed {len(changed)}; {moved} names changed defining module (ignored)")
    return 1 if total else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("take", help="write a snapshot")
    t.add_argument("out")
    t.add_argument("--root", default=".", help="worktree root (default: cwd)")
    t.add_argument("--modules", help="file with module names to snapshot instead of the default set")
    t.add_argument("--threads", type=int, default=8, help="hashing threads in the main process")
    t.add_argument("--jobs", type=int, default=3, help="concurrent Lean processes")
    t.add_argument("--no-check", action="store_true", help="skip the `lake build --no-build` freshness check")
    d = sub.add_parser("diff", help="compare two snapshots")
    d.add_argument("a")
    d.add_argument("b")
    d.add_argument("--renames", help="TSV of deliberate renames old<TAB>new (applied to A)")
    d.add_argument("--limit", type=int, default=50)
    args = ap.parse_args()
    if args.cmd == "take":
        take(args)
    else:
        sys.exit(diff(args))


if __name__ == "__main__":
    main()
