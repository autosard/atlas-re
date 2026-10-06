#!/usr/bin/env bash
# Run all example benchmarks and print a test-style summary.
#
# Usage: scripts/bench.sh [options] [MODULE_PREFIX...]
#
#   -m, --mode MODE        check (default) or infer
#   -t, --timeout SECS     timeout per benchmark (default: 600)
#   -b, --bin PATH         atlas-re binary (default: cabal list-bin exe:atlas-re,
#                          otherwise atlas-re from PATH)
#   -e, --examples DIR     examples directory (default: $ATLAS_EXAMPLES or examples)
#   -o, --out DIR          results directory (default: bench-results/<date>-<mode>)
#   -c, --compare FILE     results.tsv of an earlier run; report regressions against it
#   -x, --exclude PREFIX   skip modules with this prefix (repeatable;
#                          Data. and Potential. are always skipped)
#   -h, --help             show this help
#
# Positional MODULE_PREFIX arguments restrict the run, e.g. `Heap` or
# `SearchTree.Splay`. Each run writes results.tsv plus per-benchmark logs and
# proofs to the results directory; in infer mode also bounds.tsv with the
# inferred cost of every function, and --compare then lists changed bounds. The exit code is non-zero if any benchmark
# did not pass; with --compare, only if something regressed (a benchmark that
# passed before no longer passes, or got more than 1.5x slower).

set -uo pipefail

mode=check
timeout=600
bin=
examples=${ATLAS_EXAMPLES:-examples}
out=
compare=
excludes=(Data. Potential.)
filters=()

usage() { sed -n '2,/^$/s/^# \{0,1\}//p' "$0"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    -m|--mode)     mode=$2; shift 2 ;;
    -t|--timeout)  timeout=$2; shift 2 ;;
    -b|--bin)      bin=$2; shift 2 ;;
    -e|--examples) examples=$2; shift 2 ;;
    -o|--out)      out=$2; shift 2 ;;
    -c|--compare)  compare=$2; shift 2 ;;
    -x|--exclude)  excludes+=("$2"); shift 2 ;;
    -h|--help)     usage; exit 0 ;;
    -*)            echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
    *)             filters+=("$1"); shift ;;
  esac
done

[[ $mode == check || $mode == infer ]] || { echo "mode must be check or infer" >&2; exit 2; }
[[ -z $bin ]] && bin=$(cabal list-bin exe:atlas-re 2>/dev/null || command -v atlas-re)
[[ -x $bin ]] || { echo "atlas-re binary not found (build it or pass --bin)" >&2; exit 2; }
[[ -d $examples ]] || { echo "examples directory not found: $examples" >&2; exit 2; }
[[ -z $compare || -f $compare ]] || { echo "comparison file not found: $compare" >&2; exit 2; }

bin=$(realpath "$bin")
examples=$(realpath "$examples")
out=$(realpath -m "${out:-bench-results/$(date +%Y-%m-%d-%H%M%S)-$mode}")
mkdir -p "$out"

if [[ -t 1 && -z ${NO_COLOR:-} ]]; then
  red=$'\e[31m' green=$'\e[32m' yellow=$'\e[33m' bold=$'\e[1m' reset=$'\e[0m'
else
  red= green= yellow= bold= reset=
fi

# module name from path: Heap/Skew/Swap.atl -> Heap.Skew.Swap
modules=()
while IFS= read -r f; do
  m=${f%.atl}; m=${m//\//.}
  skip=
  for x in "${excludes[@]}"; do [[ $m == "$x"* ]] && skip=1; done
  if [[ ${#filters[@]} -gt 0 ]]; then
    match=
    for p in "${filters[@]}"; do [[ $m == "$p" || $m == "$p".* ]] && match=1; done
    [[ -z $match ]] && skip=1
  fi
  [[ -z $skip ]] && modules+=("$m")
done < <(cd "$examples" && find . -name '*.atl' -not -path './.git/*' | sed 's|^\./||' | sort)

[[ ${#modules[@]} -gt 0 ]] || { echo "no benchmarks selected" >&2; exit 2; }

rev=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
dirty=$(git status --porcelain --untracked-files=no 2>/dev/null | grep -q . && echo "+dirty")
ex_rev=$(git -C "$examples" rev-parse --short HEAD 2>/dev/null || echo unknown)

echo "${bold}atlas-re benchmarks${reset}: mode=$mode timeout=${timeout}s tool=$rev$dirty examples=$ex_rev"
echo "results: $out"
echo

results="$out/results.tsv"
printf '# mode=%s timeout=%s tool=%s%s examples=%s date=%s\n' \
  "$mode" "$timeout" "$rev" "$dirty" "$ex_rev" "$(date -Iseconds)" > "$results"
printf 'module\tstatus\tseconds\tmessage\n' >> "$results"

# inferred cost bound of every function, read from the JSON embedded in the proof
bounds="$out/bounds.tsv"
: > "$bounds"
extract_bounds() {
  python3 - "$1" "$2" <<'EOF'
import json, re, sys
module, html = sys.argv[1], open(sys.argv[2]).read()
data = json.loads(re.search(r'<script id="proof-data" type="application/json">(.*?)</script>', html, re.S).group(1))
for fn in sorted(data["functions"], key=lambda f: f["name"]):
    if fn.get("cost"):
        print(f'{module}.{fn["name"]}\t{fn["cost"]}')
EOF
}

width=0
for m in "${modules[@]}"; do (( ${#m} > width )) && width=${#m}; done

npass=0 nunsat=0 nerror=0 ntimeout=0
for m in "${modules[@]}"; do
  # the tool writes instance.smt to ./out regardless of --output, so give
  # every benchmark its own working directory
  work="$out/$m"
  mkdir -p "$work/out"
  printf '%-*s  ' "$width" "$m"

  start=$(date +%s.%N)
  (cd "$work" && timeout "$timeout" "$bin" --search "$examples" analyze \
       --analysis-mode "$mode" --output "$work/out" "$m") > "$work/log" 2>&1
  rc=$?
  secs=$(awk -v s="$start" -v e="$(date +%s.%N)" 'BEGIN { printf "%.1f", e - s }')

  if (( rc == 0 )); then
    status=PASS; msg=; ((npass++)); color=$green
  elif (( rc == 124 )); then
    status=TIMEOUT; msg="exceeded ${timeout}s"; ((ntimeout++)); color=$yellow
  elif grep -q 'No proof found' "$work/log"; then
    status=UNSAT; msg="constraint system is unsatisfiable"; ((nunsat++)); color=$red
  else
    status=ERROR; ((nerror++)); color=$red
    msg=$(sed 's/\x1b\[[0-9;]*m//g' "$work/log" | grep -v '^\s*$' | tail -1 | cut -c1-100)
  fi

  printf '%s%-7s%s %8ss  %s\n' "$color" "$status" "$reset" "$secs" "$msg"
  printf '%s\t%s\t%s\t%s\n' "$m" "$status" "$secs" "$msg" >> "$results"
  [[ $status == PASS && $mode == infer ]] && extract_bounds "$m" "$work/out/index.html" >> "$bounds"
done

total=${#modules[@]}
echo
echo "${bold}summary${reset}: $total benchmarks, ${green}$npass passed${reset}, ${red}$nunsat unsat${reset}, ${red}$nerror errors${reset}, ${yellow}$ntimeout timeouts${reset}"
failed=$(( total - npass ))

regressions=0
if [[ -n $compare ]]; then
  echo
  echo "${bold}compared with${reset} $compare ($(head -1 "$compare" | sed 's/^# //'))"
  head -1 "$compare" | grep -q "mode=$mode " ||
    echo "  ${yellow}warning:${reset} the earlier run used a different analysis mode"
  # join/comm need the same collation as sort
  export LC_COLLATE=C
  # status changes, plus slowdowns of passing benchmarks by more than 1.5x
  # (ignoring runs under 2s, where noise dominates)
  while IFS=$'\t' read -r m old_status old_secs new_status new_secs; do
    if [[ $old_status == PASS && $new_status != PASS ]]; then
      printf '  %sREGRESSED%s %-*s %s -> %s\n' "$red" "$reset" "$width" "$m" "$old_status" "$new_status"
      ((regressions++))
    elif [[ $old_status != PASS && $new_status == PASS ]]; then
      printf '  %sFIXED%s     %-*s %s -> %s\n' "$green" "$reset" "$width" "$m" "$old_status" "$new_status"
    elif [[ $old_status == PASS && $new_status == PASS ]] &&
         awk -v o="$old_secs" -v n="$new_secs" 'BEGIN { exit !(n > 2 && n > 1.5 * o) }'; then
      printf '  %sSLOWER%s    %-*s %ss -> %ss\n' "$yellow" "$reset" "$width" "$m" "$old_secs" "$new_secs"
      ((regressions++))
    elif [[ $old_status == PASS && $new_status == PASS ]] &&
         awk -v o="$old_secs" -v n="$new_secs" 'BEGIN { exit !(o > 2 && o > 1.5 * n) }'; then
      printf '  %sFASTER%s    %-*s %ss -> %ss\n' "$green" "$reset" "$width" "$m" "$old_secs" "$new_secs"
    fi
  done < <(join -t $'\t' \
             <(grep -v '^#' "$compare" | tail -n +2 | cut -f1-3 | sort) \
             <(grep -v '^#' "$results" | tail -n +2 | cut -f1-3 | sort))
  for m in $(comm -13 <(grep -v '^#' "$compare" | tail -n +2 | cut -f1 | sort) \
                      <(grep -v '^#' "$results" | tail -n +2 | cut -f1 | sort)); do
    printf '  NEW       %-*s\n' "$width" "$m"
  done
  # changed bounds are reported, but not counted as regressions: whether a
  # bound got better is not decidable by string comparison
  old_bounds="$(dirname "$compare")/bounds.tsv"
  if [[ $mode == infer && -s $old_bounds ]]; then
    while IFS=$'\t' read -r f old new; do
      [[ $old == "$new" ]] && continue
      printf '  BOUND     %-*s %s -> %s\n' "$width" "$f" "$old" "$new"
    done < <(join -t $'\t' <(sort "$old_bounds") <(sort "$bounds"))
  fi
  (( regressions == 0 )) && echo "  no regressions"
fi

if [[ -n $compare ]]; then
  (( regressions > 0 )) && exit 1
else
  (( failed > 0 )) && exit 1
fi
exit 0
