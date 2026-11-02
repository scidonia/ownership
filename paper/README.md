# Building the manuscript

`ownership-skeleton.tex` is the single canonical source. It uses the official
LIPIcs article class, `lipics-v2021`, and builds with pdfLaTeX (no shell
escape).

## Template provenance

- Series: Leibniz International Proceedings in Informatics (LIPIcs).
- Distribution: LIPIcs authors' kit, tag `v2021.1.3`.
  <https://submission.dagstuhl.de/styles/download-tag/lipics/v2021.1.3/authors/tgz>
  (retrieved 3 November 2026; archive SHA-256
  `b3aab06fab848016a954d15cbf0c1caf427c38ca8700c52f9ddd973c4cbacb48`).
- Class: `lipics-v2021.cls`, `\ProvidesClass` 2023/05/12 v3.1.3, vendored
  unmodified. SHA-256
  `ecae53dfd29c7b22d02a9065327c104760fb726a028b146d556732021a5977f0`.
- Series logo: `lipics-logo-bw.pdf` from the same kit, unmodified. SHA-256
  `23cf408069b707ff63ca2a92565197c7aa9c93a029f210fc7197e01bb37de5e0`.
- Bibliography style: `plainurl.bst` (mandatory for LIPIcs), from CTAN package
  `urlbst` 0.9.1,
  <https://mirrors.ctan.org/biblio/bibtex/contrib/urlbst/plainurl.bst>
  (retrieved 3 November 2026). SHA-256
  `3fed7ca6a2db55121e4856952f5d89655500e47e8a35af18a88f63752812f183`.
- Author instructions: the kit's `lipics-v2021-authors-guidelines.pdf` and
  `lipics-v2021-sample-article.tex`.

## Build

```bash
cd paper
latexmk -pdf -interaction=nonstopmode ownership-skeleton.tex
pdfinfo ownership-skeleton.pdf
```

Observed on 3 November 2026 with pdfTeX 3.141592653-2.6-1.40.25 (TeX Live
2023/Debian) and latexmk 4.83: exit 0, A4, **17 pages**, references beginning
on page 17.

## Page footprint

The manuscript occupies 17 pages in the LIPIcs class: the eight sections run
through page 16, and page 17 carries the acknowledgements and the bibliography
(10 entries). This is the footprint of the scientific content unchanged; the
revision plan's compression targets are measured against it.

## Warnings

The build reports no overfull boxes, no unresolved references or citations and
no missing characters. The only warnings are three `float specifier changed`
messages from the class turning `[h]` float placement into `[ht]`, and
`underfull \hbox` notices: eleven inside the ragged-right table cells (expected
for those cells) and six in justified prose. The loosest prose line reaches
badness 10000 (the paragraph at lines 603--608): it is set with emergency
stretch in place of a 4.85pt overfull line, which is the trade this document
makes for the long declaration names it quotes.

The document sets `\emergencystretch` to 3em and `\tolerance` to 300 for the
many long typewriter identifiers it quotes; the class's own 1em allowance left
a 4.85pt overfull line.

Two Unicode comparison symbols (`≤`, `≠`) have no glyphs in the class's T1 text
fonts, so they are declared to typeset from math mode where they occur inside
`\lean{...}`. Code blocks use `listings` with an explicit `literate` table for
every Unicode character the quoted Lean code contains
(`→ ∧ ∀ ∃ ≤ ≠ ∈ ⟨ ⟩ …`); no glyph is dropped and no shell escape is required.

## Proceedings metadata and anonymity

`\EventEditors`, `\EventNoEds`, the event title, `\SeriesVolume` and
`\ArticleNo` are left unset because no volume or article number has been
assigned; none is invented. The class consequently prints its own placeholder
DOI line (`10.4230/LIPIcs...`) and `XX` page numbers in the running heads until
those fields are filled in.

The article class's `\date` line is not part of the LIPIcs title block and the
class has no date metadata field, so the draft date the previous layout printed
under the author is not displayed. The dates inside the text (the observations
at `d330fa0`) are unchanged.

The class's `anonymous` option (documentclass option, which blanks the author,
affiliation, email and copyright holder) is not enabled: LIPIcs is a
single-blind, author-named series, and the 2027 event's anonymity rule could
not be confirmed. If the call for papers requires anonymisation, add
`anonymous` to the `\documentclass` options rather than maintaining a second
source file.
