#!/usr/bin/env bash

set -euo pipefail

NAME="$(sed -n 's/^name = "\([^"]*\)"/\1/p' lakefile.toml | head -n1)"
if [ -z "$NAME" ]; then
  echo "Failed to parse package name from lakefile.toml" >&2
  exit 1
fi

TOOLCHAIN_REV="$(cut -d: -f2 lean-toolchain)"
if [ -z "$TOOLCHAIN_REV" ]; then
  echo "Failed to parse lean-toolchain revision" >&2
  exit 1
fi

TARGETS_RAW="$(sed -n 's/^defaultTargets = \[\(.*\)\]/\1/p' lakefile.toml | head -n1)"
if [ -z "$TARGETS_RAW" ]; then
  TARGETS_RAW="\"$NAME\""
fi

DOCS_FACETS="$(
  echo "$TARGETS_RAW" \
    | tr ',' '\n' \
    | sed -E 's/[[:space:]"]//g' \
    | sed '/^$/d' \
    | awk '{printf "%s:docs ", $0}'
)"
DOCS_FACETS="${DOCS_FACETS% }"

mkdir -p docbuild
cat <<EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "$NAME"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$TOOLCHAIN_REV"
EOF

cd docbuild
if [ -f ../references.bib ]; then
  mkdir -p docs
  cp ../references.bib ./docs/references.bib
fi
MATHLIB_NO_CACHE_ON_UPDATE=1 ~/.elan/bin/lake update "$NAME"

# A restored docgen cache can contain the `*.docs_built` marker without the
# corresponding static files in `.lake/build/doc`.  In that state Lake skips
# doc generation and then fails while tracing files such as `doc/style.css`.
if [ -d .lake/build/doc-data ]; then
  find .lake/build/doc-data -name '*.docs_built' -delete
fi

~/.elan/bin/lake build $DOCS_FACETS
