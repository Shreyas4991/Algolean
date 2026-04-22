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

# Prefer the doc-gen4 rev the project's existing manifest already resolved:
# transitive deps (e.g. Physlib) often pin doc-gen4 to a rev that doesn't
# match our toolchain tag, and the shallow clone fetched by lean-action only
# contains that rev. Asking for a different tag here makes `lake update` fail
# with "revision not found" even when the tag exists upstream.
DOC_GEN_REV="${DOC_GEN_REV:-}"
if [ -z "$DOC_GEN_REV" ] && [ -f lake-manifest.json ] && command -v jq >/dev/null 2>&1; then
  DOC_GEN_REV="$(
    jq -r '[.packages[]? | select((.name // "") | gsub("«|»"; "") == "doc-gen4") | .inputRev // empty][0] // empty' lake-manifest.json \
      || true
  )"
fi
if [ -z "$DOC_GEN_REV" ]; then
  DOC_GEN_REV="$TOOLCHAIN_REV"
  if ! git ls-remote --exit-code --tags https://github.com/leanprover/doc-gen4 "refs/tags/$DOC_GEN_REV" >/dev/null 2>&1; then
    echo "doc-gen4 has no tag '$DOC_GEN_REV'; falling back to 'main'" >&2
    DOC_GEN_REV="main"
  fi
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
rev = "$DOC_GEN_REV"
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
