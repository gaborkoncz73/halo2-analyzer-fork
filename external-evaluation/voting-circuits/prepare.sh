#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# Az eredeti kiadas ellenorzott csomagjahoz csak az elemzoi hozzaferest adja hozza.
version=0.3.5
checksum=f5aca1c66059a919227dec97444a11a4350d2f9c820ca48690988f0aa0e81cbf
backend="target/halo2_proofs-$version"
patch_file="$PWD/halo2-analyzer-visibility.patch"
mkdir -p target
if [[ -d "$backend" ]]; then
    git -C "$backend" apply --reverse --check "$patch_file"
    printf 'Halo2 %s analyzer backend is already prepared.\n' "$version"
    exit 0
fi

archive="$PWD/target/halo2_proofs-$version.crate"
cached="${CARGO_HOME:-$HOME/.cargo}/registry/cache"
found=false
for candidate in "$cached"/*/"halo2_proofs-$version.crate"; do
    if [[ -f "$candidate" ]]; then
        cp -- "$candidate" "$archive"
        found=true
        break
    fi
done
if [[ "$found" == false ]]; then
    curl --fail --location --retry 2 --max-time 120 \
        "https://static.crates.io/crates/halo2_proofs/halo2_proofs-$version.crate" \
        --output "$archive"
fi
printf '%s  %s\n' "$checksum" "$archive" | sha256sum --check
stage=$(mktemp -d "$PWD/target/backend-XXXXXX")
tar -xzf "$archive" -C "$stage"
git -C "$stage/halo2_proofs-$version" apply --check "$patch_file"
git -C "$stage/halo2_proofs-$version" apply "$patch_file"
mv -- "$stage/halo2_proofs-$version" "$backend"
rmdir -- "$stage"
printf 'Prepared Halo2 %s with analyzer visibility only.\n' "$version"
