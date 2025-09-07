#!/usr/bin/env bash

TOOL="atlas-re --search /usr/share/atlas/examples/leftist-heaps"

# Define examples (module -> description)
declare -A EXAMPLES=(
  [SkewHeapST]="Skew heap with piece-wise potential Φ_[t<u]"
  [SkewHeap2]="Skew heap with sum-of-logs potential Φ_u"
  [SkewHeap3over2]="Skew heap with sum-of-logs potential Φ_(-t)"
  [SkewHeapGolden]="Skew heap with sum-oflogs potential Φ_ϕ"
  [Swap]="Swap operation"
  [WeightBiased]="Weight-biased leftist heap with sum-of-logs potential Φ_ϕ"
  [WeightBiasedWC]="Worst-case analysis for weight-biased leftist heap"
  [RankBiased]="Rank-biased leftist heap with rank potential."
  [RankBiased]="Worst-case analysis for rank-biased leftist heap."
  [SkewHeapSTValue]="Skew heap with piece-wise potential Φ_[t<u] and value variables."
  [SkewHeap3over2Value]="Skew heap with sum-of-logs potential Φ_(-t) and value variables."
  [RankBiasedValue]="Rank biased leftist heap with rank potential and value variables."
)

list_examples() {
  echo "Available examples:"
  for key in "${!EXAMPLES[@]}"; do
    printf "  %-23s %s\n" "$key" "${EXAMPLES[$key]}"
  done | sort
}

run_analysis() {
  local example="$1"
  local mode="$2"
  shift 2
  echo "Running: $TOOL analyze --analysis-mode $mode $@ $example"
  $TOOL analyze --analysis-mode "$mode" "$@" "$example"
}

usage() {
  cat <<EOF
Usage: $0 <command> [options]

Commands:
  list-examples               List available example modules.
  infer <example> [args...]   Run analysis in infer mode.
  check <example> [args...]   Run analysis in check-cost mode.
EOF
}

if [[ $# -lt 1 ]]; then
  usage
  exit 1
fi

command="$1"
shift

case "$command" in
  list-examples)
    list_examples
    ;;
  infer)
    if [[ -z "$1" ]]; then
      echo "Error: example required" >&2
      usage
      exit 1
    fi
    example="$1"
    shift
    run_analysis "$example" infer "$@"
    ;;
  check)
    if [[ -z "$1" ]]; then
      echo "Error: example required" >&2
      usage
      exit 1
    fi
    example="$1"
    shift
    run_analysis "$example" check-coeffs "$@"
    ;;
  *)
    echo "Unknown command: $command" >&2
    usage
    exit 1
    ;;
esac
