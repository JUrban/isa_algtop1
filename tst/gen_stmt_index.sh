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
            if any(ls.startswith(k) for k in ['proof','sorry','oops','by ','unfolding','using']) and j > i:
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
        else:
            def_m = re.search(r'"([^"]{1,400})', flat)
            sig = def_m.group(1) if def_m else flat[:300]
        # strip Isabelle unicode escapes for searchability
        sig = re.sub(r'\\<(\w+)>', r'\1', sig)
        sig = sig.replace('\n', ' ')
        if len(sig) > 400:
            sig = sig[:397] + '...'
        print(f'{f}:{i+1} {kind} {name} :: {sig}')
    i += 1
PYEND
done

total=$(wc -l < "$OUT")
echo "Statement index: $total entries -> $OUT"
