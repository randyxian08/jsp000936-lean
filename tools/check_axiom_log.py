#!/usr/bin/env python3
"""Check actual #print axioms output from a successful Lean invocation."""
import json
import re
import sys
from pathlib import Path
if len(sys.argv)!=2:
    raise SystemExit('usage: check_axiom_log.py path/to/axioms.log')
p=Path(sys.argv[1]); text=p.read_text()
allowed={'propext','Classical.choice','Quot.sound'}
expected={'JSPFreeNodes.jsp_000936','JSPFreeNodes.jsp_000937_classification',
          'JSPFreeNodes.canonical_allMinPeak_eq_one','JSPFreeNodes.allMinPeak_le_any_amplification',
          'JSPInterpolation.jsp_000958_maximum'}
found={name: {x.strip() for x in body.split(',') if x.strip()}
       for name,body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",text,re.S)}
for name in re.findall(r"'([^']+)' does not depend on any axioms",text): found[name]=set()
missing=expected-found.keys()
extra={name:sorted(axes-allowed) for name,axes in found.items() if axes-allowed}
report={'missing_declarations':sorted(missing),'nonstandard_axioms':extra,
        'observed_axioms':{k:sorted(v) for k,v in found.items()},
        'result':'pass' if not missing and not extra else 'fail',
        'scope':'available declarations only, NOT the full 937 task'}
p.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
raise SystemExit(bool(missing or extra))
