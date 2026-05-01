#!/usr/bin/env bash
# Run cvc5 to generate an Alethe proof for an SMT-LIB file, then check it
# with Carcara, using the same options as the cvc5 regression harness.
#
# The proof is saved next to the input file as <input>.alethe.
#
# Usage:    test-alethe.sh <input.smt2> [extra cvc5 options...]
#
# Anything after the input file is forwarded to cvc5, so you can do e.g.
#   test-alethe.sh foo.smt2 --nl-ext --tlimit=10000
#
# Edit the variables below to change binaries or options.

CVC5_BIN=/home/hbarbosa/cvc5/wt-dratt/prod/bin/cvc5
CARCARA_BIN=/home/hbarbosa/carcara/target/release/carcara
RARE_FILE=/home/hbarbosa/carcara/rewrites.eo

CVC5_OPTS=(
    --proof-format=alethe
    --dump-proofs
    --proof-granularity=dsl-rewrite
    --proof-elim-subtypes
)

CARCARA_OPTS=(
    --allow-int-real-subtyping
    --expand-let-bindings
    --allowed-rules undefined arrays_select_const
    --rare-file $RARE_FILE
)

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <input.smt2> [extra cvc5 options...]" >&2
    exit 2
fi

input="$1"
shift
CVC5_EXTRA=("$@")

if [[ ! -f "$input" ]]; then
    echo "error: file not found: $input" >&2
    exit 2
fi

proof="${input}.alethe"

echo ">>> $CVC5_BIN ${CVC5_OPTS[*]} ${CVC5_EXTRA[*]} $input"
echo ">>> writing proof to: $proof"
raw=$("$CVC5_BIN" "${CVC5_OPTS[@]}" "${CVC5_EXTRA[@]}" "$input" 2>&1)

# Detect cases where cvc5 produced no actual proof body. The alethe printer
# emits `(error "Proof unsupported by Alethe: ...")` instead of a real proof
# when it encounters an unsupported operator/rule. cvc5 may also emit other
# diagnostic lines (e.g. "unknown", "sat") in place of `unsat`.
if [[ "$raw" != "unsat"* ]]; then
    echo "warning: cvc5 did not produce an unsat proof" >&2
    printf '%s\n' "$raw" >&2
    exit 1
fi
if grep -q "Proof unsupported by Alethe" <<<"$raw"; then
    echo "warning: cvc5 did not generate a proof (unsupported by Alethe):" >&2
    grep "Proof unsupported by Alethe" <<<"$raw" >&2
    exit 1
fi

# Strip the leading `unsat\n(\n` and trailing `\n)` (or `)` on the same line)
# from the cvc5 wrapper. Matches run_regression.py's strip_proof_body.
if [[ "$raw" != $'unsat\n(\n'* ]]; then
    echo "warning: unexpected cvc5 output (missing 'unsat\\n(\\n' header)" >&2
    printf '%s\n' "$raw" >&2
    exit 1
fi
raw="${raw#$'unsat\n(\n'}"
raw="${raw%$'\n)'}"
printf '%s\n' "$raw" > "$proof"

echo ">>> $CARCARA_BIN check ${CARCARA_OPTS[*]} $proof $input"
out=$("$CARCARA_BIN" check "${CARCARA_OPTS[@]}" "$proof" "$input" 2>&1)
rc=$?
printf '%s\n' "$out"
case "$out" in
    *valid*|*holey*)
        echo "SUCCESS"
        exit 0
        ;;
    *)
        echo "FAILURE"
        exit "${rc:-1}"
        ;;
esac
