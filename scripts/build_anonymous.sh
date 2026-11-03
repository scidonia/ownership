#!/usr/bin/env bash
#
# Build the anonymous version of the paper from the one canonical source.
#
#   bash scripts/build_anonymous.sh
#
# The derivation is mechanical and is not kept in the repository: the source in
# paper/ownership-skeleton.tex is the only copy. The script
#   1. copies the paper's sources to a temporary directory,
#   2. adds the `anonymous` class option (which makes lipics-v2021 hide the
#      author block, the copyright line and the PDF metadata author),
#   3. blanks the acknowledgements section (the class anonymises the author
#      block itself once the option is set),
#   4. builds and writes paper/ownership-skeleton-anonymous.pdf, and
#   5. fails if the author's name, affiliation or address survives anywhere in
#      the extracted text, and fails if the build is not the anonymous one.
set -euo pipefail
cd "$(dirname "$0")/.."

src=paper
out="$src/ownership-skeleton-anonymous.pdf"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cp "$src/ownership-skeleton.tex" "$src/lipics-v2021.cls" "$src/plainurl.bst" \
   "$src/references.bib" "$src/lipics-logo-bw.pdf" "$tmp/"

# 1. the class option
sed -i 's/^\\documentclass\[\(.*\)\]{lipics-v2021}$/\\documentclass[\1,anonymous]{lipics-v2021}/' \
  "$tmp/ownership-skeleton.tex"

# 2. blank the acknowledgements section (up to the bibliography)
awk '
  /^\\section\*\{Acknowledgements\}/ { skip = 1 }
  /^\\bibliographystyle\{/ { skip = 0 }
  !skip { print }
' "$tmp/ownership-skeleton.tex" > "$tmp/anonymous.tex"
mv "$tmp/anonymous.tex" "$tmp/ownership-skeleton.tex"

# 4. build
( cd "$tmp" && latexmk -pdf -interaction=nonstopmode ownership-skeleton.tex >/dev/null 2>&1 )
cp "$tmp/ownership-skeleton.pdf" "$out"

# 5. verify that nothing identifying survives, and that this is the anonymous build
text=$(pdftotext "$out" -)
status=0
for needle in "Mendel-Gleason" "Scidonia Limited" "gavin@scidonia.ai"; do
  if printf '%s' "$text" | grep -Fq "$needle"; then
    echo "anonymity check FAILED: '$needle' appears in $out" >&2
    status=1
  fi
done
if ! printf '%s' "$text" | grep -Fiq "Anonymous author"; then
  echo "anonymity check FAILED: no 'Anonymous author' marker in $out" >&2
  status=1
fi

pages=$(pdfinfo "$out" | awk '/^Pages:/ {print $2}')
echo "wrote $out ($pages pages)"

exit "$status"
