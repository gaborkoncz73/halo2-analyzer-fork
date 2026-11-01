#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

revision=4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4
archive_checksum=b6a0d6d036b161e6daa29e550fb375059fc9c15b715abe2b685ab8429bd12f01
upstream="target/halo2-soundness-bugs-$revision"
archive="$PWD/target/upstream-$revision.tar.gz"
mkdir -p target

verify_sources() {
    printf '%s  %s\n' \
        60135cb0d47026832300c0c7ae0efb60697cf772c7fa1e65bd62847b75f9213a "$upstream/src/square_root/sroot0.rs" \
        908e56f6a919734a29c4ba83ea0ad21667224424fd0c3d51a65bc7aa93ec68eb "$upstream/src/square_root/sroot1.rs" \
        2d1302c6246fa1555dd03e8cbe12c6e38111753b74b8a57b22172cfc2bdec38b "$upstream/src/casino/casino2.rs" \
        25b673dbcc8013af289bb76e7039b40934c1ceedceee982ef0e050dfd6a58afe "$upstream/src/merkle/merkle_nohash4.rs" \
        | sha256sum --check
}

# A kulso circuit forrasat valtoztatas nelkul, rogzitett commitbol kesziti elo.
if [[ -d "$upstream" ]]; then
    verify_sources
else
    if [[ ! -f "$archive" ]]; then
        curl --fail --location --retry 2 --max-time 120 \
            "https://codeload.github.com/teddav/halo2-soundness-bugs/tar.gz/$revision" \
            --output "$archive"
    fi
    printf '%s  %s\n' "$archive_checksum" "$archive" | sha256sum --check
    tar -xzf "$archive" -C target
    verify_sources
fi

# A helyi kontroll kulon masolatot kap; az eredeti kulso forras valtozatlan marad.
control="$PWD/target/casino-first-deposit-control"
patch_file="$PWD/casino-first-deposit.patch"
mkdir -p "$control"
cp -- "$upstream/src/casino/casino2.rs" "$control/casino2.rs"
git -C "$control" apply --check "$patch_file"
git -C "$control" apply "$patch_file"
printf '%s  %s\n' fbfbaa5be794716c6d77b53de15bf1c7d571dfdf9181c1c1e718e6ceaf1b120e "$control/casino2.rs" | sha256sum --check
printf 'Prepared separately identified casino first-deposit control.\n'

# A kis tablas kontroll csak a lookup meretet valtoztatja, nem az elemzo szabalyait.
for variant in casino-small-lookup-original casino-small-lookup-repaired; do
    destination="$PWD/target/$variant"
    mkdir -p "$destination"
    cp -- "$upstream/src/casino/casino2.rs" "$destination/casino2.rs"
    git -C "$destination" apply "$PWD/casino-small-lookup.patch"
    if [[ "$variant" == casino-small-lookup-repaired ]]; then
        git -C "$destination" apply "$patch_file"
    fi
done
printf '%s  %s\n' \
    95009267bcf0cd8ee6941be6b49bbfb4524a1acf71a27eb7c17475eab64cbaed "$PWD/target/casino-small-lookup-original/casino2.rs" \
    2e0e34d0ae4fd52e59412893b308ed5a1f5be967895d0ff2a0d50f27eeb8b4dc "$PWD/target/casino-small-lookup-repaired/casino2.rs" \
    | sha256sum --check
printf 'Prepared separately identified 16-entry lookup controls.\n'
