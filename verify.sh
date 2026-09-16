#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export PATH="$HOME/.elan/bin:$PATH"
echo 'Verified scopes: JSP-000936 real interval; JSP-000937 classification ONLY.'
echo 'Full JSP-000937 remains incomplete: logarithmic upper bound is not supplied.'
lake env lean --version
lake exe cache get
lake build Erdos1153.JSPInterpolation.Regression Erdos1153.JSPInterpolation.JSP958
lake env lean Audit936.lean
lake env lean AuditAvailable.lean 2>&1 | tee verification-axioms.log
python3 tools/check_axiom_log.py verification-axioms.log
if grep -R -n -E --include='*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|sorryAx|native_decide|implemented_by)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe|opaque)[[:space:]]' \
  Erdos1153 Erdos1153.lean Audit936.lean AuditAvailable.lean; then
  echo 'Source trust scan failed' >&2
  exit 1
fi
echo 'ALL DECLARED SCOPES PASSED; FULL JSP-000937 NOT CLAIMED.'
