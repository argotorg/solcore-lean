#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"

if ! cmp -s lean-toolchain ../lean-toolchain; then
  echo "Manual and library Lean toolchains differ." >&2
  exit 1
fi

export TMPDIR="${TMPDIR:-$PWD/.lake/tmp}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mkdir -p "$TMPDIR"

toolchain=$(cat lean-toolchain)
expected_version=${toolchain##*:v}
case "$(lake --version)" in
  *"(Lean version $expected_version)"*) ;;
  *) echo "Select $toolchain for both Lean and Lake before building." >&2; exit 1 ;;
esac

lake build Guide
render_dir=$(mktemp -d "$PWD/.lake/render.XXXXXX")
trap 'rm -rf "$render_dir"' EXIT HUP INT TERM
lake env lean --run Main.lean --output "$render_dir" --without-tex --depth 1 \
  --with-html-single --with-html-multi
test -s "$render_dir/html-single/index.html"
test -s "$render_dir/html-multi/index.html"
mkdir -p _out
for edition in html-single html-multi; do
  rm -rf "_out/$edition"
  mv "$render_dir/$edition" "_out/$edition"
done
