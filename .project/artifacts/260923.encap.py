# ai-disclosure: ai-generated
#
# Throwaway tooling for .project/260923.plan.encapsulation.md.  Not part of
# the development and not maintained: delete this file when the plan is
# finished.  Every subcommand either reads, or edits files in place and
# prints what it did; nothing is committed.  Run from anywhere.
#
#   census [--internal | --clashes | --name X]
#   sectargs FILE [--out JSON]            needs a fresh `dune build`
#   split-inline [--dry-run]              workstream A
#   localize FILE [--dry-run]             workstream B
#   rename --file F --module M --begin B --end E --map TSV [--dry-run]
#                                         workstream C
#   codediff --old REV:PATH... --new PATH... [--ignore-qualifiers]
#            [--map TSV]                  supplemental textual comparison
#
# Every check that fails prints a line starting with HANDBACK and exits 2.
# The plan says what to do then: stop and ask, do not work around it.

import glob, json, os, re, subprocess, sys, collections, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.chdir(ROOT)

V_FILES = sorted(glob.glob('theories/*.v') + glob.glob('dev/*.v')
                 + glob.glob('dev/check/*.v') + glob.glob('expect-test/*.v')
                 + ['extraction/Extract.v'])
API_FILES = sorted(glob.glob('harness/*.ml') + ['dist/README.md']
                   + glob.glob('dist/check/*.ml') + glob.glob('expect-test/*.t'))

DECL = re.compile(
    r'^[ \t]*((?:#\[[^\]]*\][ \t]*)?(?:Local[ \t]+|Global[ \t]+)*)'
    r'(Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Corollary|Example|Fact|'
    r'Remark|Proposition|Inductive|Variant|Record|Structure|Class|Instance|'
    r'Notation|Ltac|Let|Variable|Hypothesis)[ \t]+'
    r"([A-Za-z_][A-Za-z0-9_']*)", re.M)
IDENT = re.compile(r"(?<![A-Za-z0-9_'.])((?:[A-Za-z_][A-Za-z0-9_']*\.)*)"
                   r"([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])")
LOCALIZABLE = {'Definition', 'Fixpoint', 'Lemma', 'Fact', 'Remark'}
RENAMEABLE = {'Definition', 'Fixpoint', 'Lemma', 'Theorem', 'Corollary',
              'Example', 'Fact', 'Remark', 'Proposition'}


def handback(msg):
    print('HANDBACK: ' + msg)
    sys.exit(2)


# ---------------------------------------------------------------------------
# Lexing: comments and strings blanked, offsets and newlines kept.

def mask(s, ocaml=False, keep_strings=False):
    """Return (code, comment) masks of s: each keeps only its own
    characters, everything else blanked to spaces (newlines kept).
    String literals are blanked unless keep_strings is requested."""
    code, com = list(s), list(s)
    i, n = 0, len(s)

    def blank(buf, a, b):
        for k in range(a, b):
            if buf[k] != '\n':
                buf[k] = ' '
    last = 0
    while i < n:
        if s.startswith('(*', i):
            d, j = 0, i
            while j < n:
                if s.startswith('(*', j): d += 1; j += 2
                elif s.startswith('*)', j):
                    d -= 1; j += 2
                    if d == 0: break
                elif s[j] == '"' and not ocaml:
                    k = j + 1
                    while k < n and not (s[k] == '"' and s[k + 1:k + 2] != '"'):
                        k += 2 if s[k] == '"' else 1
                    j = k + 1
                else: j += 1
            blank(com, last, i); blank(code, i, j); last = j; i = j
        elif s[i] == '"':
            j = i + 1
            while j < n:
                if s[j] == '"':
                    if not ocaml and s[j + 1:j + 2] == '"': j += 2; continue
                    if ocaml and s[j - 1] == '\\': j += 1; continue
                    break
                j += 1
            if not keep_strings: blank(code, i, j + 1)
            i = j + 1
        elif ocaml and s[i] == "'" and i + 2 < n and s[i + 2] == "'":
            blank(code, i, i + 3); i += 3
        else:
            i += 1
    blank(com, last, n)
    return ''.join(code), ''.join(com)


def line_of(s, off):
    return s.count('\n', 0, off) + 1


def line_offsets(s):
    offs = [0]
    for m in re.finditer('\n', s):
        offs.append(m.end())
    return offs   # offs[k] = offset of line k+1


# ---------------------------------------------------------------------------
# Declarations and sections of one file.

def declarations(path, text=None):
    s = text if text is not None else open(path).read()
    code, _ = mask(s)
    out = []
    for m in DECL.finditer(code):
        prefix, kind, name = m.group(1), m.group(2), m.group(3)
        line = line_of(code, m.start())
        before = s[:m.start()].rstrip()
        doc = False
        if before.endswith('*)'):
            k = before.rfind('(*')
            doc = before[k:k + 3] == '(**'
        out.append(dict(name=name, kind=kind, line=line, off=m.start(),
                        kwoff=m.start(2), local='Local' in prefix
                        or '#[local]' in prefix, doc=doc))
        if kind in ('Inductive', 'Variant', 'Record', 'Structure', 'Class'):
            end = code.find('.\n', m.end())
            body = code[m.end():end]
            names = re.findall(r"\|\s*([A-Za-z_][A-Za-z0-9_']*)", body)
            names += re.findall(r"[{;]\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", body)
            mm = re.search(r":=\s*([A-Za-z_][A-Za-z0-9_']*)\s*\{", body)
            if mm: names.append(mm.group(1))
            for c in names:
                out.append(dict(name=c, kind=kind + '-member', line=line,
                                off=m.start(), kwoff=None, local=False,
                                doc=False))
    return out


SECT_OPEN = re.compile(r'^[ \t]*(Section|Module)[ \t]+([A-Za-z_]\w*)[ \t]*\.[ \t]*$', re.M)
SECT_END = re.compile(r'^[ \t]*End[ \t]+([A-Za-z_]\w*)[ \t]*\.[ \t]*$', re.M)


def section_stack_at(path, text=None):
    """Map line -> tuple of open (kind, name, open_line) at that line."""
    s = text if text is not None else open(path).read()
    code, _ = mask(s)
    events = []
    for m in SECT_OPEN.finditer(code):
        events.append((line_of(code, m.start()), 'open', m.group(1), m.group(2)))
    for m in SECT_END.finditer(code):
        events.append((line_of(code, m.start()), 'end', None, m.group(1)))
    events.sort()
    nlines = code.count('\n') + 1
    stacks, stack, ev = {}, [], 0
    for ln in range(1, nlines + 1):
        while ev < len(events) and events[ev][0] == ln:
            _, what, kind, name = events[ev]
            if what == 'open': stack.append((kind, name, ln))
            else:
                if not stack or stack[-1][1] != name:
                    handback(f'{path}:{ln}: End {name} does not match the open section')
                stack.pop()
            ev += 1
        stacks[ln] = tuple(stack)
    return stacks


def section_ends(path, text=None):
    """Map an opening line to the line of its matching `End`."""
    s = text if text is not None else open(path).read()
    code, _ = mask(s)
    events = []
    for m in SECT_OPEN.finditer(code):
        events.append((line_of(code, m.start()), 'open', m.group(2)))
    for m in SECT_END.finditer(code):
        events.append((line_of(code, m.start()), 'end', m.group(1)))
    events.sort()
    stack, ends = [], {}
    for ln, what, name in events:
        if what == 'open': stack.append((ln, name))
        else:
            if stack: ol, _ = stack.pop(); ends[ol] = ln
    return ends


def section_header(path, sect, upto, text=None):
    """The `Context` lines of section `sect` (kind,name,open_line) that
    appear before line `upto`, its section-local `Ltac` definitions (a
    close-and-reopen copies them), and every other section-local construct
    a close-and-reopen would lose."""
    s = text if text is not None else open(path).read()
    code, _ = mask(s)
    lines = code.split('\n')
    raw = s.split('\n')
    contexts, hazards, ltacs = [], [], []
    depth = 0
    for ln in range(sect[2] + 1, upto):
        t = lines[ln - 1]
        if depth == 0 and re.match(r'Ltac\b', t.strip()):
            k = ln
            while k < len(lines) and not (lines[k - 1].rstrip().endswith('.')
                                          and not lines[k].strip()):
                k += 1
            ltacs.append((ln, '\n'.join(raw[ln - 1:k])))
            continue
        if SECT_OPEN.match(t): depth += 1; continue
        if SECT_END.match(t): depth -= 1; continue
        if depth: continue
        st = t.strip()
        if st.startswith('Context'):
            if not st.endswith('.'):
                hazards.append((ln, 'multi-line Context'))
            elif re.match(r'Context\s*\(', st):
                hazards.append((ln, 'explicit Context argument'))
            contexts.append(raw[ln - 1].strip())
        elif re.match(r'(Variable|Variables|Hypothesis|Hypotheses|Let|'
                      r'Local Ltac|Local Notation|Notation|#\[local\])\b', st):
            hazards.append((ln, st.split()[0] + ' ' + (st.split()[1] if len(st.split()) > 1 else '')))
    return contexts, hazards, ltacs


# ---------------------------------------------------------------------------
# Users of a name across the repository.

_TOKENS = None


def tokens_by_file():
    global _TOKENS
    if _TOKENS is None:
        _TOKENS = {}
        for f in V_FILES + API_FILES:
            if not os.path.exists(f): continue
            s = open(f).read()
            if f.endswith('.md'):
                code = s
            else:
                code, _ = mask(s, ocaml=f.endswith('.ml'))
            toks = set()
            for m in IDENT.finditer(code):
                toks.add(m.group(2)); toks.add(m.group(1) + m.group(2))
            _TOKENS[f] = toks
    return _TOKENS


def users(name, exclude=None):
    return sorted(f for f, toks in tokens_by_file().items()
                  if name in toks and f != exclude)


def frozen_names():
    """Names whose OCaml path is public: named by the harness, the dist
    README and checks, or the extraction prelude."""
    names = set()
    for f in API_FILES:
        if not os.path.exists(f): continue
        for m in re.finditer(r'\bDjot(?:_fixtures)?\.[A-Z]\w*\.([a-z_]\w*)', open(f).read()):
            names.add(m.group(1))
    ext = open('extraction/Extract.v').read()
    m = re.search(r'Separate Extraction(.*?)\.\s*$', ext, re.S | re.M)
    if m: names.update(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", m.group(1)))
    names.update(n.split('.')[-1] for n in re.findall(r'Extract Constant\s+([\w.]+)', ext))
    return names


# ---------------------------------------------------------------------------
# census

def cmd_census(args):
    decls = [(f, d) for f in sorted(glob.glob('theories/*.v')) for d in declarations(f)]
    if '--clashes' in args:
        seen = collections.defaultdict(list)
        for f, d in decls:
            if d['kind'] not in ('Variable', 'Hypothesis', 'Let'):
                seen[d['name']].append(f'{f}:{d["line"]}')
        for n, where in sorted(seen.items()):
            if len({w.split(':')[0] for w in where}) > 1:
                print(n, ' '.join(where))
        return
    if '--name' in args:
        n = args[args.index('--name') + 1]
        for f, d in decls:
            if d['name'] == n: print('declared', f, d['line'], d['kind'])
        print('used in', ' '.join(users(n)))
        return
    for f, d in decls:
        ext = users(d['name'], exclude=f)
        if '--internal' in args and (ext or d['local']): continue
        print(f"{f}:{d['line']}\t{d['kind']}\t{d['name']}\t"
              f"{'local' if d['local'] else ''}\t{len(ext)}\t{' '.join(ext)}")


# ---------------------------------------------------------------------------
# sectargs: the section variables each sectioned declaration takes.

def logical_path(path):
    if path.startswith('theories/'):
        return 'DjotV.' + os.path.basename(path)[:-2]
    if path.startswith('dev/check/'):
        return 'DjotVDev.check.' + os.path.basename(path)[:-2]
    if path.startswith('dev/'):
        return 'DjotVDev.' + os.path.basename(path)[:-2]
    handback(f'{path}: not a theory file')


def sectargs(path):
    stacks = section_stack_at(path)
    names = [d for d in declarations(path)
             if d['kind'] in RENAMEABLE | {'Instance'}
             and any(k == 'Section' for k, _, _ in stacks.get(d['line'], ()))]
    if not names: return {}
    mod = logical_path(path)
    probe = ['From Stdlib Require Import String.', f'Require {mod}.']
    for d in names:
        probe.append(f'Goal True. idtac "##{d["name"]}". Abort.')
        probe.append(f'About {mod}.{d["name"]}.')
    with tempfile.NamedTemporaryFile('w', suffix='.v', delete=False, dir='/tmp') as t:
        t.write('\n'.join(probe) + '\n'); tmp = t.name
    r = subprocess.run(['rocq', 'c', '-R', '_build/default/theories', 'DjotV',
                        '-R', '_build/default/dev', 'DjotVDev', tmp],
                       capture_output=True, text=True)
    os.unlink(tmp)
    if r.returncode != 0:
        handback('sectargs probe failed (is `dune build` fresh?):\n' + r.stderr[-2000:])
    out, cur, ctxvars = {}, None, {}
    for d in names:
        vs = []
        for sect in stacks[d['line']]:
            if sect[0] == 'Section':
                ctx, _, _ = section_header(path, sect, d['line'])
                for c in ctx:
                    vs += re.findall(r"[{(`]\s*([A-Za-z_][\w' ]*?)\s*:", c)
        ctxvars[d['name']] = [v for group in vs for v in group.split()]
    for line in r.stdout.split('\n'):
        m = re.match(r'##(\S+)', line)
        if m: cur = m.group(1); out[cur] = []; continue
        m = re.match(r'Arguments\s+\S+\s*(.*)', line)
        if m and cur is not None and not out[cur]:
            lead = []
            for grp in re.finditer(r'\{([^}]*)\}|\(([^)]*)\)|(\S+)', m.group(1)):
                items = (grp.group(1) or grp.group(2) or grp.group(3)).split()
                stop = False
                for it in items:
                    it = it.split('%')[0]
                    if it in ctxvars.get(cur, []): lead.append(it)
                    else: stop = True; break
                if stop: break
            out[cur] = lead
    return out


def cmd_sectargs(args):
    res = sectargs(args[0])
    js = json.dumps(res, indent=0, sort_keys=True)
    if '--out' in args: open(args[args.index('--out') + 1], 'w').write(js)
    else: print(js)


# ---------------------------------------------------------------------------
# Token rewriting that respects comments and strings.

def rewrite_tokens(text, fn, in_comments=True):
    """fn(qualifier, name, is_code) -> replacement string or None."""
    code, com = mask(text)
    out, pos = [], 0
    spans = []
    for buf, is_code in ((code, True), (com, False)):
        if not is_code and not in_comments: continue
        for m in IDENT.finditer(buf):
            r = fn(m.group(1), m.group(2), is_code)
            if r is not None and r != m.group(0):
                spans.append((m.start(), m.end(), r))
    spans.sort()
    for a, b, r in spans:
        out.append(text[pos:a]); out.append(r); pos = b
    out.append(text[pos:])
    return ''.join(out), len(spans)


def add_section_args(text, targets, args_of):
    """`@X` -> `@X T ...` in code, for X in targets, unless the section
    arguments are already spelled out.  A shadowing binder (e.g. a lemma's
    own `{LI : LineIx}`) makes the source write them itself; prepending
    again would pass two instances."""
    code, _ = mask(text)
    out, pos, n = [], 0, 0
    for m in re.finditer(r"@((?:[A-Za-z_][\w']*\.)*[A-Za-z_][\w']*)", code):
        name = m.group(1).split('.')[-1]
        if name not in targets or not args_of.get(name):
            continue
        args = args_of[name]
        if re.match(r'(?:\s+' + r'\s+'.join(map(re.escape, args)) + r')(?![\w\'])',
                    code[m.end():]):
            continue
        out.append(text[pos:m.end()]); out.append(' ' + ' '.join(args))
        pos = m.end(); n += 1
    out.append(text[pos:])
    return ''.join(out), n


# ---------------------------------------------------------------------------
# split-inline (workstream A).  Line numbers are those of theories/Inline.v
# at commit 155a400; the anchors check that nothing moved since.

SPLIT_ANCHORS = {20: 'Local Open Scope string_scope.', 835: 'Section WithTable.',
                 836: 'Context {T : dtable}.', 1974: '(*', 1975: 'The inline pass',
                 4279: '(*', 4280: 'The located scan', 5721: '(*',
                 5722: 'The output frame', 9150: '(*', 9151: 'The key connective',
                 9386: '(*', 9387: 'The pass inverts the view', 9438: '(*',
                 9439: 'The renderer', 9596: '(*', 9597: 'Escapes, pinned',
                 9605: 'End WithTable.',
                 5616: 'Lemma iscan_str_app :', 5621: 'Qed.',
                 5732: 'Definition istart : iscan := IText false EmptyString None ostart.',
                 9001: "(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`",
                 9006: '  ifinish (iscan_lines l istart).',
                 9369: "(* The canonical view's paragraph, laid out the same way. *)",
                 9384: 'Proof. reflexivity. Qed.',
                 9617: '#[export] Instance djot_table : dtable :=',
                 9629: '  DTable markdown_like_config eq_refl.'}

SPLIT_PARTS = [
    # (file, [(first, last)], in_section, header).  Ranges are copied in
    # the order listed; the moved declarations go to the end of the part
    # they now belong to, after everything they use.
    ('theories/InlineTable.v', [(21, 834)], False,
     'The delimiter table: the characters the scanner claims, the table of\n'
     '   delimiter rows as a parameter, its admissibility condition, and the\n'
     '   checked row updates.  The class `dtable` packages an admissible table.'),
    ('theories/InlineView.v', [(837, 1973), (9369, 9385), (9438, 9595)], True,
     'The table in force, the escape encoding, the canonical inline view\n'
     '   `cinline` with its source (`ci_src`), AST (`ci_ast`) and conditions\n'
     '   (`ci_ok`), the canonical paragraph (`ci_para`), and the renderer.'),
    ('theories/InlineScan.v', [(1974, 4278), (5732, 5732), (6596, 6598), (5616, 5622),
                               (9001, 9017), (9107, 9127), (9150, 9368)], True,
     'The inline pass: the single-pass scanner over a paragraph\'s text, its\n'
     '   scope stack, the line-level drivers, `para_inlines`, and the key\n'
     '   connective (`.project/keyed-blocks.md`).'),
    ('theories/InlineLocated.v', [(4279, 5615), (9018, 9106)], True,
     'The located scan, and erasure: the located and semantic scans agree\n'
     '   once coordinates are dropped.'),
    ('theories/InlineInvert.v', [(5623, 5731), (5733, 6595), (6599, 9000), (9128, 9149),
                                 (9386, 9437)], True,
     'The scan inverts the canonical view: scanning a canonical line reaches\n'
     '   the state that emitting its nodes reaches, and a canonical paragraph\n'
     '   parses back to its inlines.'),
]
SPLIT_AGG_RANGE = (9606, 9630)
SPLIT_EXAMPLES = ('dev/InlineExamples.v', [(9596, 9604), (9631, None)])
SECTION_LTACS = ['sem_flush']   # section-local tactics a later part may need
SPLIT_IMPORTS = {
    'InlineTable': [],
    'InlineView': ['InlineTable'],
    'InlineScan': ['InlineTable', 'InlineView'],
    'InlineLocated': ['InlineTable', 'InlineView', 'InlineScan'],
    'InlineInvert': ['InlineTable', 'InlineView', 'InlineScan'],
}


def cmd_split_inline(args):
    dry = '--dry-run' in args
    src_path = 'theories/Inline.v'
    s = open(src_path).read()
    baseline = subprocess.run(['git', 'show', '155a400:theories/Inline.v'],
                              capture_output=True, text=True, check=True).stdout
    if s != baseline:
        handback('Inline.v differs from the pinned 155a400 source; re-plan the split')
    raw = s.split('\n')
    coverage = collections.Counter()
    for _, ranges, _, _ in SPLIT_PARTS:
        for a, b in ranges:
            coverage.update(range(a, b + 1))
    expected = set(range(21, 9596)) - {835, 836}
    if set(coverage) != expected or any(n != 1 for n in coverage.values()):
        handback('split ranges must cover the implementation exactly once')
    for ln, want in SPLIT_ANCHORS.items():
        if raw[ln - 1].rstrip() != want:
            handback(f'{src_path}:{ln} is {raw[ln - 1]!r}, expected {want!r}; '
                     'the file changed since the plan was written')
    args_of = sectargs(src_path)
    decls = declarations(src_path)
    owner = {}          # declared name -> part file
    for part, ranges, _, _ in SPLIT_PARTS:
        for d in decls:
            if any(a <= d['line'] <= b for a, b in ranges):
                owner.setdefault(d['name'], part)
    agg = [d['name'] for d in decls if SPLIT_AGG_RANGE[0] <= d['line'] <= SPLIT_AGG_RANGE[1]]
    ltac_text = {}
    for name in SECTION_LTACS:
        m = re.search(r'^Ltac ' + name + r' :=.*?\.\n(?=\n)', s, re.S | re.M)
        if not m: handback(f'Ltac {name} not found')
        ltac_text[name] = (m.group(0), line_of(s, m.start()))
    header_imports = ('From Stdlib Require Import String Ascii List Bool Lia Wf_nat Arith.\n'
                      'From DjotV Require Import Config Strings Ast Attributes')
    written, prev = {}, []
    for part, ranges, in_sect, head in SPLIT_PARTS:
        body = '\n'.join('\n'.join(raw[a - 1:b]) for a, b in ranges)
        mod = os.path.basename(part)[:-2]
        earlier = {n for n, p in owner.items() if p != part and p in prev_files(prev)}
        body, n_at = add_section_args(body, earlier, args_of)
        copies = ''
        for name, (txt, ln) in ltac_text.items():
            defined_here = any(a <= ln <= b for a, b in ranges)
            used = re.search(r'\b' + name + r'\b', mask(body)[0])
            if used and not defined_here:
                t2, _ = add_section_args(txt, {n for n, p in owner.items() if p != part}, args_of)
                copies += t2 + '\n'
        imports = header_imports + ''.join(' ' + p for p in SPLIT_IMPORTS[mod]) + '.\n'
        text = ('(* ai-disclosure: autonomous *)\n\n(* ' + head + ' *)\n\n' + imports
                + 'Import ListNotations.\n\nLocal Open Scope string_scope.\n\n')
        if in_sect:
            text += 'Section WithTable.\nContext {T : dtable}.\n\n' + copies
        text += body.strip('\n') + '\n'
        if in_sect: text += '\nEnd WithTable.\n'
        written[part] = text
        print(f'{part}: {sum(b - a + 1 for a, b in ranges)} source lines, '
              f'{n_at} `@name` gained section arguments'
              + (', copied ' + ', '.join(ltac_text) if copies else ''))
        prev.append(part)
    parts_mods = ' '.join(os.path.basename(p)[:-2] for p, _, _, _ in SPLIT_PARTS)
    agg_text = ('\n'.join(raw[0:14]) + '\n\n'
                '(* The inline layer is split across the files re-exported here, in\n'
                '   dependency order; this file adds the delimiter table instances. *)\n\n'
                'From Stdlib Require Import String.\n'
                'From DjotV Require Export ' + parts_mods + '.\n\n'
                'Local Open Scope string_scope.\n\n'
                + '\n'.join(raw[SPLIT_AGG_RANGE[0] - 1:SPLIT_AGG_RANGE[1]]).strip('\n') + '\n')
    written[src_path] = agg_text
    ex_path, ex_ranges = SPLIT_EXAMPLES
    ex_body = '\n'.join('\n'.join(raw[a - 1:(b if b else len(raw))]) for a, b in ex_ranges)
    written[ex_path] = ('(* ai-disclosure: autonomous *)\n\n'
                        '(* Examples pinning the inline scanner at djot\'s table, each\n'
                        '   checked against djot.js.  Nothing requires this file. *)\n\n'
                        'From Stdlib Require Import String Ascii List Bool Lia Arith.\n'
                        'From DjotV Require Import Config Strings Ast Attributes Inline.\n'
                        'Import ListNotations.\n\nLocal Open Scope string_scope.\n\n'
                        + ex_body.strip('\n') + '\n')
    # qualified `Inline.X` elsewhere now names the part that declares X
    requal = {}
    for f in V_FILES:
        if f == src_path: continue
        t = open(f).read()
        def fn(q, name, is_code):
            if q in ('Inline.', 'DjotV.Inline.') and name in owner:
                return q[:-len('Inline.')] + os.path.basename(owner[name])[:-2] + '.' + name
            return None
        t2, n = rewrite_tokens(t, fn)
        if n: requal[f] = t2; print(f'{f}: {n} qualified `Inline.` references re-pointed')
    moved_api = sorted(n for n in frozen_names() if n in owner)
    if moved_api:
        print('OCaml API paths that move out of `Inline`: ' + ', '.join(
            f'{n} -> {os.path.basename(owner[n])[:-2]}' for n in moved_api))
    if dry: print('dry run: nothing written'); return
    for p, t in list(written.items()) + list(requal.items()):
        open(p, 'w').write(t)
    print('written; aggregator declares: ' + ', '.join(agg))


def prev_files(prev):
    return set(prev)


# ---------------------------------------------------------------------------
# localize (workstream B)

# R1 (resolved 2026-09-24): intended entry points, customization functions
# and predicates named by exported theorem statements stay public even when
# nothing outside their file uses them.  The named exceptions are below; the
# statement rule is computed per file by public_names().
PUBLIC = {
    ('Wf.v', 'wf_doc'),                 # the top-level well-formedness predicate
    ('Site.v', 'route'),                # the routing entry point
    ('Site.v', 'routes_ok'),            # the SSG check, the first thing to run
    ('Address.v', 'resolve_top_id'),    # the address resolution entry point
    ('Profile.v', 'with_inline_profile'),   # a customization function
    ('Profile.v', 'with_block_profile'),    # its companion
}

STMT_STOP = re.compile(r'\b(Proof|Qed|Admitted|Defined|Abort)\b|:=')


def statement_span(code, d):
    """The statement (type) of a declaration: its keyword up to the first
    `Proof`/`Qed`/... or `:=`.  Used to keep predicates an exported
    theorem statement names."""
    if d['kwoff'] is None: return ''
    m = STMT_STOP.search(code, d['kwoff'])
    return code[d['kwoff']:m.start()] if m else code[d['kwoff']:]


def public_names(path, s):
    """R1: names in `path` that stay public -- the named entry points,
    everything a public declaration is, and every name a public
    declaration's statement mentions (transitively)."""
    decls = [d for d in declarations(path, s) if d['kwoff'] is not None]
    code, _ = mask(s)
    base = os.path.basename(path)
    public = {n for f, n in PUBLIC if f == base}
    public |= {d['name'] for d in decls
               if d['kind'] not in LOCALIZABLE or d['doc']
               or users(d['name'], exclude=path)}
    for _ in range(4):
        added = set()
        for d in decls:
            if d['name'] in public:
                for m in IDENT.finditer(statement_span(code, d)):
                    added.add(m.group(2))
        new = added - public
        public |= new
        if not new: break
    return public


def cmd_localize(args):
    path = args[0]
    dry = '--dry-run' in args
    if not path.startswith('theories/'): handback('localize runs on theories/ only')
    s = open(path).read()
    frozen = frozen_names()
    public = public_names(path, s)
    done, skipped = [], collections.Counter()
    edits = []
    for d in declarations(path, s):
        if d['kwoff'] is None or d['local']: continue
        if d['kind'] not in LOCALIZABLE: skipped[d['kind']] += 1; continue
        if d['doc']: skipped['doc-comment'] += 1; continue
        if d['name'] in frozen: skipped['frozen'] += 1; continue
        if d['name'] in public: skipped['public-policy'] += 1; continue
        if users(d['name'], exclude=path): continue
        edits.append(d['kwoff']); done.append(d['name'])
    for off in sorted(edits, reverse=True):
        s = s[:off] + 'Local ' + s[off:]
    print(f'{path}: {len(done)} declarations made Local; kept public by rule: '
          + ', '.join(f'{k} {v}' for k, v in sorted(skipped.items())))
    for n in done: print('  ' + n)
    if not dry: open(path, 'w').write(s)


# ---------------------------------------------------------------------------
# rename (workstream C)

RESERVED = set('''Set Prop Type SProp forall fun match with end as in return if then else
let fix cofix struct Proof Qed Defined Admitted Lemma Theorem Definition Fixpoint
Module End Section Context Import Export Require From
nat bool list option string ascii prod sum unit True False and or not eq
true false Some None nil cons pair fst snd id app rev map length filter fold_left
fold_right hd tl last nth In incl existsb forallb find combine split concat
flat_map seq repeat firstn skipn negb andb orb implb xorb S O plus mult minus
pred min max
inline inlines block blocks node attr doc span spot pos'''.split())


def cmd_rename(args):
    def opt(k):
        if k not in args: handback(f'missing {k}')
        return args[args.index(k) + 1]
    path, mod = opt('--file'), opt('--module')
    begin, end = int(opt('--begin')), int(opt('--end'))
    dry = '--dry-run' in args
    mp = {}
    for ln in open(opt('--map')):
        if ln.strip() and not ln.startswith('#'):
            a, b = ln.split()
            if a in mp: handback(f'{a} mapped twice')
            mp[a] = b
    if len(set(mp.values())) != len(mp): handback('two old names map to one new name')
    if not re.fullmatch(r'[A-Z][A-Za-z0-9]*', mod): handback('module name must be CamelCase')
    basenames = {os.path.basename(f)[:-2] for f in glob.glob('theories/*.v') + glob.glob('dev/**/*.v', recursive=True)}
    if mod in basenames: handback(f'module {mod} has the name of a file')
    stdlib = {'List', 'String', 'Ascii', 'Nat', 'Bool', 'Decimal', 'Hexadecimal',
              'Number', 'Byte', 'Init', 'Logic', 'Datatypes', 'Peano', 'Arith',
              'Lia', 'Wf_nat', 'ListDef', 'PeanoNat', 'BinNat', 'BinPos', 'Pos',
              'N', 'Z', 'Q', 'Option', 'Prelude', 'Specif', 'Sumbool', 'Program'}
    if mod in stdlib: handback(f'module {mod} has the name of a Stdlib module')
    for f in V_FILES:
        if re.search(r'^\s*Module\s+' + mod + r'\b', open(f).read(), re.M):
            handback(f'module {mod} already exists in {f}: module names must be unique')
    frozen = frozen_names()
    bad = sorted(set(mp) & frozen)
    if bad: print('FROZEN OCaml API names in the map (migrate consumers in '
                  'this commit): ' + ', '.join(bad))
    s = open(path).read()
    decls = declarations(path, s)
    inside = [d for d in decls if begin <= d['line'] <= end]
    for d in inside:
        if d['name'] not in mp:
            handback(f'{path}:{d["line"]}: {d["kind"]} {d["name"]} is in the range but not in the map')
        if d['kind'] not in RENAMEABLE:
            handback(f'{path}:{d["line"]}: a {d["kind"]} cannot move into a module by this tool')
    declared = {d['name'] for d in inside}
    for a in mp:
        if a not in declared: handback(f'{a} is not declared in {path}:{begin}-{end}')
    code, _ = mask(s)
    offs = line_offsets(s)
    rng_code = code[offs[begin - 1]:offs[end] if end < len(offs) else len(code)]
    present = {m.group(2) for m in IDENT.finditer(rng_code) if not m.group(1)}
    for a, b in mp.items():
        if b in RESERVED: handback(f'new name {b} is reserved (shadows a common name)')
        if not re.fullmatch(r"[a-z_][A-Za-z0-9_']*", b): handback(f'bad new name {b}')
        if b in present and b not in mp:
            handback(f'new name {b} already occurs in the range; renaming would capture it')
    stacks = section_stack_at(path, s)
    if stacks[begin] != stacks[end]:
        handback('the range starts and ends at different section depths')
    if any(k == 'Module' for k, _, _ in stacks[begin]):
        handback('the range is inside a module already')
    sects = [x for x in stacks[begin] if x[0] == 'Section']
    headers = []
    sect_names = {d['name'] for d in decls
                  if sects and stacks.get(d['line'], ())[:len(sects)] == tuple(sects)}
    for sect in sects:
        ctx, hz, ltacs = section_header(path, sect, end + 1, s)
        if hz:
            handback(f'section {sect[1]} has constructs a close-and-reopen would lose: '
                     + '; '.join(f'line {l}: {w}' for l, w in hz))
        copies = []
        for ln, txt in ltacs:
            if ln >= begin:
                handback(f'{path}:{ln}: an Ltac defined inside the range or after it '
                         'would be lost at the module boundary')
            for m in re.finditer(r"@([A-Za-z_][\w']*)", mask(txt)[0]):
                if m.group(1) in sect_names:
                    handback(f'{path}:{ln}: section-local Ltac uses @{m.group(1)}, '
                             'which a copy outside the section cannot spell')
            copies.append(txt)
        headers.append((sect[1], ctx + copies))
    # section arguments: names of the same file whose section is cut here
    args_of = sectargs(path) if sects else {}
    seg_of = {}
    for d in decls:
        if not sects or not (stacks.get(d['line']) and stacks[d['line']][:len(sects)] == tuple(sects)):
            continue
        seg_of[d['name']] = 0 if d['line'] < begin else (1 if d['line'] <= end else 2)
    # rewrite this file
    lines = s.split('\n')
    segs = ['\n'.join(lines[:begin - 1]), '\n'.join(lines[begin - 1:end]), '\n'.join(lines[end:])]
    fname = os.path.basename(path)[:-2]

    def renamer(segment):
        def fn(q, name, is_code):
            if name not in mp: return None
            if q in ('', fname + '.', 'DjotV.' + fname + '.'):
                if segment == 1 and q == '': return mp[name]
                return q + mod + '.' + mp[name]
            return None
        return fn
    new_segs, total = [], 0
    # The innermost original section ends at `outer_end`; code past it was
    # never inside that section, so closing and reopening does not affect
    # how its `@name` references are written.
    outer_end = section_ends(path, s).get(sects[-1][2]) if sects else None
    for i, seg in enumerate(segs):  # 0 before the range, 1 inside, 2 after
        t, n = rewrite_tokens(seg, renamer(i)); total += n
        if sects:
            targets = {nm for nm, sg in seg_of.items() if sg != i}
            renamed_args = {}
            for nm in targets:
                if nm in args_of:
                    renamed_args[nm] = args_of[nm]
                    if nm in mp: renamed_args[mp[nm]] = args_of[nm]
            tnames = targets | {mp[n] for n in targets if n in mp}
            if i == 2 and outer_end is not None:
                parts = t.split('\n')
                cut = outer_end - end
                head = '\n'.join(parts[:cut])
                tail = '\n'.join(parts[cut:])
                head, k = add_section_args(head, tnames, renamed_args)
                t = head + '\n' + tail
            else:
                t, k = add_section_args(t, tnames, renamed_args)
            total += k
        new_segs.append(t)
    close = ''.join(f'End {n}.\n' for n, _ in reversed(headers))
    reopen = ''.join(f'Section {n}.\n' + ''.join(c + '\n' for c in ctx) for n, ctx in headers)
    s2 = (new_segs[0].rstrip('\n') + '\n\n' + close + f'Module {mod}.\n\n' + reopen
          + ('\n' if reopen else '') + new_segs[1].strip('\n') + '\n\n' + close
          + f'End {mod}.\n\n' + reopen + ('\n' if reopen else '') + new_segs[2].lstrip('\n'))
    others = {}
    for f in V_FILES:
        if f == path: continue
        t = open(f).read()
        def fn(q, name, is_code):
            if name not in mp: return None
            if q in ('', fname + '.', 'DjotV.' + fname + '.'):
                return q + mod + '.' + mp[name]
            return None
        t2, n = rewrite_tokens(t, fn)
        if n: others[f] = t2; print(f'{f}: {n} references')
    print(f'{path}: {total} rewrites, module {mod} wraps lines {begin}-{end}'
          + (f', sections {", ".join(n for n, _ in headers)} closed and reopened' if headers else ''))
    if dry: print('dry run: nothing written'); return
    open(path, 'w').write(s2)
    for f, t in others.items(): open(f, 'w').write(t)


# ---------------------------------------------------------------------------
# codediff

WRAPPER = re.compile(r'^(Section|End|Context|Module|From|Require|Import|Local Open Scope)\b')


def code_lines(text, ignore_q, rmap):
    code, _ = mask(text, keep_strings=True)
    # Preserve literal bytes, including whitespace and newlines, before
    # normalizing layout or names. This is still a textual review aid.
    code = re.sub(r'"(?:[^"]|"")*"',
                  lambda m: '__encap_literal_' + m.group(0).encode().hex(), code)
    out = collections.Counter()
    for l in code.split('\n'):
        l = ' '.join(l.split())
        if not l or WRAPPER.match(l): continue
        # section arguments the tools insert: drop the leading run of them
        # after every `@name`, in old and new alike, so both normalize alike
        l = re.sub(r"(@[\w.']+)((?: (?:T|K|LI|P)\b)+)", r"\1", l)
        if ignore_q:
            l = IDENT.sub(lambda m: m.group(2), l)
        for a, b in rmap.items():
            l = re.sub(r'(?<![\w\'.])' + re.escape(b) + r'(?![\w\'])', a, l)
        out[l] += 1
    return out


def cmd_codediff(args):
    olds = args[args.index('--old') + 1:args.index('--new')]
    news = [a for a in args[args.index('--new') + 1:] if not a.startswith('--')]
    if '--ignore-qualifiers' in args:
        news = [a for a in news if a != '--ignore-qualifiers']
    rmap = {}
    if '--map' in args:
        mapfile = args[args.index('--map') + 1]
        news = [a for a in news if a != mapfile]
        for ln in open(mapfile):
            if ln.strip() and not ln.startswith('#'):
                a, b = ln.split(); rmap[a] = b
    iq = '--ignore-qualifiers' in args
    old, new = collections.Counter(), collections.Counter()
    for spec in olds:
        rev, p = spec.split(':', 1)
        old += code_lines(subprocess.run(['git', 'show', f'{rev}:{p}'], capture_output=True,
                                         text=True, check=True).stdout, iq, rmap)
    for p in news:
        new += code_lines(open(p).read(), iq, rmap)
    gone, added = old - new, new - old
    for l, c in sorted(gone.items()): print('-', l, f'x{c}' if c > 1 else '')
    for l, c in sorted(added.items()): print('+', l, f'x{c}' if c > 1 else '')
    print(f'{sum(gone.values())} lines only in old, {sum(added.values())} only in new')


if __name__ == '__main__':
    cmd, rest = sys.argv[1], sys.argv[2:]
    {'census': cmd_census, 'sectargs': cmd_sectargs, 'split-inline': cmd_split_inline,
     'localize': cmd_localize, 'rename': cmd_rename, 'codediff': cmd_codediff}[cmd](rest)
