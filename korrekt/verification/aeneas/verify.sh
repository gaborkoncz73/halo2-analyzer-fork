#!/usr/bin/env bash
set -euo pipefail

here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
source "$here/versions.env"
mode="${1:---check}"
if [[ "$#" -gt 1 || ( "$mode" != --check && "$mode" != --update ) ]]; then
    printf 'Hasznalat: bash %s [--check|--update]\n' "$0" >&2
    exit 2
fi

tools="$here/.tools"
if [[ ! -x "$tools/aeneas/charon" || ! -x "$tools/lean/bin/lake" ]]; then
    printf 'Elobb futtassa: bash %s/bootstrap.sh\n' "$here" >&2
    exit 1
fi
[[ "$("$tools/aeneas/aeneas" -version)" == "aeneas $AENEAS_RELEASE" ]]
[[ "$("$tools/aeneas/charon" version)" == *"$CHARON_COMMIT"* ]]
[[ "$("$tools/lean/bin/lean" --version)" == *"version $LEAN_VERSION"* ]]
export PATH="$tools/lean/bin:$PATH"

work="$(mktemp -d "$tools/verify.XXXXXX")"
trap 'rm -rf -- "$work"' EXIT

# Az eredeti forrasfajlokbol ujra kinyeri a kovetkeztetes es a fociklus hivasgrafjat.
(
    cd "$here/rust"
    "$tools/aeneas/charon" cargo --preset=aeneas --sysroot default \
        --start-from 'crate::rules::expression_is_unique' \
        --start-from 'crate::rules::infer_assigned_cell_from_zero_equation_with_modulus' \
        --start-from 'crate::recovery_loop::run_recovery' \
        --start-from 'crate::mark_unique' \
        --start-from 'crate::mark_initial_unique' \
        --start-from 'crate::domain_entrypoints' \
        --start-from 'crate::recovery_core::merge_established_evidence' \
        --start-from 'crate::recovery_core::finish_merge' \
        --dest-file "$work/ucp_verified.llbc" -- --locked
)
"$tools/aeneas/aeneas" -backend lean -split-files -impl-namespace -filter-trait-methods \
    -use-lean-modules false -no-progress-bar -dest "$work/lean" "$work/ucp_verified.llbc"

# Kizarolag a konstruktorok nevet minositi: az Aeneas none metodusa kulonben elrejti az Option.none-t.
perl -pi -e 's/(?<![.\w])none\b/Option.none/g; s/(?<![.\w])some\b/Option.some/g' "$work/lean/Funs.lean"
# A Rust-tipusokat Type 0-ban ertelmezi; nem igenyel univerzumpolimorf Rust-ertekeket.
perl -pi -e 's/\bType _/Type/g' "$work/lean/Types.lean" "$work/lean/Funs.lean"

(
    cd "$root"
    sha256sum korrekt/src/circuit_analyzer/ucp/{cell,expr,facts,rules,recovery_loop,recovery_core,privacy,privacy_search,value,value_inference,profiling}.rs \
        korrekt/verification/aeneas/rust/{lib.rs,Cargo.toml,Cargo.lock} \
        korrekt/verification/aeneas/versions.env
) > "$work/SOURCES.sha256"

if [[ "$mode" == --update ]]; then
    mkdir -p "$here/generated"
    cp "$work/ucp_verified.llbc" "$here/generated/ucp_verified.llbc"
    cp "$work/SOURCES.sha256" "$here/generated/SOURCES.sha256"
    cp "$work/lean/Types.lean" "$work/lean/Funs.lean" "$here/lean/UcpVerified/"
else
    for file in Types.lean Funs.lean; do
        diff -u "$here/lean/UcpVerified/$file" "$work/lean/$file"
    done
    diff -u "$here/generated/SOURCES.sha256" "$work/SOURCES.sha256"
    # Az LLBC-t a kimeneti ut es a forraspozicio-metaadatok nelkul veti ossze.
    # A standard konyvtari makrok pozicioi gepenkent elterhetnek; a program tartalma nem.
    # A pozicioval kepzett Source-sorok a Funs.lean fenti osszevetesebe tovabbra is beleszamitanak.
    normalize='.translated.options.dest_file = null | walk(if type == "object" then del(.span) else . end)'
    jq -c "$normalize" "$here/generated/ucp_verified.llbc" > "$work/recorded.json"
    jq -c "$normalize" "$work/ucp_verified.llbc" > "$work/current.json"
    if ! cmp "$work/recorded.json" "$work/current.json"; then
        diff <(jq . "$work/recorded.json") <(jq . "$work/current.json") | head -60 || true
        exit 1
    fi
fi

cd "$here/lean"
lake build
printf '\nForras -> Charon -> Aeneas -> Lean: sikeres ellenorzes.\n'
