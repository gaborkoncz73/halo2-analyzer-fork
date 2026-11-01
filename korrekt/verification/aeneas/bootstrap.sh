#!/usr/bin/env bash
set -euo pipefail

here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
source "$here/versions.env"
tools="$here/.tools"
mkdir -p "$tools"

# A korabbi ideiglenes telepites megszunt celjara mutato linkeket helyi telepitesre csereli.
for tool in aeneas lean; do
    if [[ -L "$tools/$tool" && ! -e "$tools/$tool" ]]; then
        unlink "$tools/$tool"
    fi
done

if [[ "$(uname -sm)" != "Linux x86_64" ]]; then
    printf 'A rogzitett binaris csomag Linux x86_64 rendszert igenyel.\n' >&2
    exit 1
fi

if [[ ! -x "$tools/aeneas/aeneas" ]]; then
    curl --fail --location --retry 3 \
        "https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_RELEASE/aeneas-linux-x86_64.tar.gz" \
        -o "$tools/aeneas.tar.gz"
    printf '%s  %s\n' "$AENEAS_SHA256" "$tools/aeneas.tar.gz" | sha256sum --check -
    mkdir -p "$tools/aeneas"
    tar -xzf "$tools/aeneas.tar.gz" -C "$tools/aeneas"
fi

if [[ ! -x "$tools/lean/bin/lake" ]]; then
    curl --fail --location --retry 3 \
        "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.tar.zst" \
        -o "$tools/lean.tar.zst"
    printf '%s  %s\n' "$LEAN_SHA256" "$tools/lean.tar.zst" | sha256sum --check -
    mkdir -p "$tools/lean"
    tar -xf "$tools/lean.tar.zst" --strip-components=1 -C "$tools/lean"
fi

rustup toolchain install "$RUST_TOOLCHAIN" --profile minimal --component rustc-dev,rust-src

export PATH="$tools/lean/bin:$PATH"
cd "$here/lean"
lake update
# Az elore forditott Mathlib-gyorsitotarat hasznalja, ha elerheto; hianyaban a build leforditja.
lake exe cache get || true
printf '\nAeneas es a rogzitett fuggoosegek elokeszitve.\n'
