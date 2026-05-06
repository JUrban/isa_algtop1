#!/bin/bash
# Generate a searchable theorem statement index.
# Each entry: file:line KIND name :: statement_fragment
# Usage: cd /project/tst && bash gen_stmt_index.sh
# Then search: grep "keyword" STMT_INDEX.txt

THEORIES=(
  i/Top1_Ch2.thy i/Top1_Ch3.thy i/Top1_Ch4.thy i/Top1_Ch5_8.thy i/Top1_Ch9_13.thy
  h/AlgTopHelpers.thy b0/AlgTop_JCT_Base0.thy b/AlgTop_JCT_Base.thy
  a0/AlgTop0.thy ac/AlgTopCached.thy AlgTop.thy
)

OUT=STMT_INDEX.txt

> "$OUT"
for f in "${THEORIES[@]}"; do
  [ -f "$f" ] || continue
  python3 - "$f" >> "$OUT" << 'PYEND'
import re, sys
f = sys.argv[1]
lines = open(f).readlines()
i = 0
while i < len(lines):
    m = re.match(r'^(lemma|theorem|corollary|definition)\s+(\S+)', lines[i].strip())
    if m:
        kind, name = m.group(1), m.group(2).rstrip(':')
        # collect statement lines until proof/sorry/oops/by/where/begin
        stmt = []
        j = i
        while j < min(len(lines), i+25):
            l = lines[j].rstrip()
            stmt.append(l.strip())
            ls = l.strip()
            if any(ls.startswith(k) for k in ['proof','sorry','oops','by ','unfolding','using',
                    'lemma','theorem','corollary','definition','text','section','subsection','end']) and j > i:
                break
            j += 1
        # flatten to one line
        flat = ' '.join(stmt)
        # extract shows/assumes or definition body
        shows_m = re.search(r'shows\s+"([^"]{1,400})', flat)
        assumes_m = re.search(r'assumes\s+"([^"]{1,200})', flat)
        if shows_m:
            sig = shows_m.group(1)
            if assumes_m:
                sig = assumes_m.group(1)[:100] + ' ==> ' + sig
        elif kind == 'definition':
            # For definitions, prefer the where "..." clause (the body)
            where_m = re.search(r'where\s+"([^"]{1,500})', flat)
            if where_m:
                sig = where_m.group(1)
            else:
                # Fall back to type signature
                type_m = re.search(r'::\s+"([^"]{1,200})', flat)
                sig = type_m.group(1) if type_m else flat[:300]
        else:
            def_m = re.search(r'"([^"]{1,400})', flat)
            sig = def_m.group(1) if def_m else flat[:300]
        # Map Isabelle unicode escapes to readable ASCII
        sym_map = {
            'forall': 'ALL ', 'exists': 'EX ', 'nexists': '~EX ',
            'in': ' : ', 'notin': ' ~: ', 'subseteq': ' <= ',
            'subset': ' < ', 'supseteq': ' >= ',
            'union': ' Un ', 'inter': ' Int ', 'Union': 'UN', 'Inter': 'IN',
            'Rightarrow': ' => ', 'Longrightarrow': ' ==> ',
            'longrightarrow': ' --> ', 'longleftrightarrow': ' <-> ',
            'and': ' & ', 'or': ' | ', 'not': '~',
            'lambda': '%', 'Lambda': '%',
            'equiv': ' == ', 'noteq': ' ~= ',
            'le': ' <= ', 'ge': ' >= ', 'times': ' * ',
            'circ': ' o ', 'lbrakk': '[', 'rbrakk': ']',
            'open': '', 'close': '',
            'pi': 'pi', 'sigma': 'sigma', 'tau': 'tau',
            'alpha': 'a', 'beta': 'b', 'gamma': 'g',
            'iota': 'iota', 'phi': 'phi', 'Phi': 'Phi', 'Psi': 'Psi',
        }
        def replace_sym(m):
            name = m.group(1)
            return sym_map.get(name, name)
        sig = re.sub(r'\\<(\w+)>', replace_sym, sig)
        sig = re.sub(r'\s+', ' ', sig).strip()
        if len(sig) > 500:
            sig = sig[:497] + '...'
        print(f'{f}:{i+1} {kind} {name} :: {sig}')
    i += 1
PYEND
done

total=$(wc -l < "$OUT")
echo "Statement index: $total entries -> $OUT"
