#!/bin/sh

set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

count_lines() {
  find "$@" -type f -name '*.v' -exec wc -l {} + |
    awk '$2 != "total" { total += $1 } END { print total + 0 }'
}

probability=$(count_lines theories/Probability)
logic=$(count_lines theories/ProgramLogics theories/NextMessage)
security=$(count_lines theories/Security)
schemes=$(count_lines theories/Schemes theories/Constructions)
adapters=$(count_lines theories/LibExtras)
total=$((probability + logic + security + schemes + adapters))

printf '%-42s %8s\n' "Layer" "Lines"
printf '%-42s %8d\n' "Probability, KL, Gaussian analysis" "$probability"
printf '%-42s %8d\n' "Program logics and trace syntax" "$logic"
printf '%-42s %8d\n' "Security proofs and reduction" "$security"
printf '%-42s %8d\n' "Schemes and construction" "$schemes"
printf '%-42s %8d\n' "MathComp/SSProve adapters" "$adapters"
printf '%-42s %8d\n' "Total" "$total"
