#!/usr/bin/env bash
set -euo pipefail

PAPER_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ARXIV_DIR="$PAPER_DIR/arxiv"
METADATA="${ARXIV_METADATA:-$ARXIV_DIR/ARXIV_METADATA.txt}"
TEXBIN="${TEXBIN:-}"
PYTHON_BIN="${PYTHON:-python3}"
ARXIV_OUTPUT_DIR="${ARXIV_OUTPUT_DIR:-${TMPDIR:-/tmp}/erdos36-arxiv-render}"

if [[ -d "$TEXBIN" ]]; then
  export PATH="$TEXBIN:$PATH"
fi
for tool in "$PYTHON_BIN" pdflatex bibtex tar pdfinfo pdftoppm rg; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf 'error: %s is required (set TEXBIN if TeX Live is not on PATH)\n' "$tool" >&2
    exit 1
  }
done
[[ -f "$METADATA" ]] || {
  printf 'error: arXiv metadata not found: %s\n' "$METADATA" >&2
  exit 1
}

TMP_ROOT="$(mktemp -d /tmp/erdos36-arxiv.XXXXXX)"
cleanup() { rm -rf "$TMP_ROOT"; }
trap cleanup EXIT
SOURCE_DIR="$TMP_ROOT/source"
INITIAL_BUILD="$TMP_ROOT/initial-build"
EXTRACT_DIR="$TMP_ROOT/extracted"
mkdir -p "$SOURCE_DIR" "$INITIAL_BUILD" "$EXTRACT_DIR"

"$PYTHON_BIN" - "$METADATA" "$PAPER_DIR/main.tex" "$SOURCE_DIR/main.tex" <<'PY'
from pathlib import Path
import re
import sys

metadata_path, conference_path, output_path = map(Path, sys.argv[1:])
fields = {}
for block in metadata_path.read_text(encoding="utf-8").strip().split("\n\n"):
    label, sep, value = block.partition("\n")
    if not sep:
        continue
    key = label.strip().rstrip(":")
    if key in fields:
        raise SystemExit(f"duplicate metadata field: {key}")
    fields[key] = value.strip()
for key in ("Title", "Authors", "Abstract", "Affiliation", "Email", "Website", "ORCID"):
    if not fields.get(key):
        raise SystemExit(f"missing metadata field: {key}")
if len(fields["Abstract"]) > 1920:
    raise SystemExit("arXiv limits abstracts to 1920 characters")
author_name = fields["Authors"]
affiliation = fields["Affiliation"]
email = fields["Email"]
website = fields["Website"]
orcid = fields["ORCID"]
orcid_id = re.sub(r"^https?://orcid\.org/", "", orcid).strip()
if not re.fullmatch(r"\d{4}-\d{4}-\d{4}-\d{3}[\dX]", orcid_id, re.I):
    raise SystemExit("ORCID must be a validated 16-character ID or orcid.org URL")
if not re.fullmatch(r"https://[^\s{}]+", website):
    raise SystemExit("Website must be an HTTPS URL")
if not re.fullmatch(r"[^@{}\s]+@[^@{}\s]+", email):
    raise SystemExit("Email must be a single email address")

source = conference_path.read_text(encoding="utf-8")
if source.count(r"\begin{document}") != 1:
    raise SystemExit("expected exactly one document body in paper/main.tex")
if source.count(r"\keywords{") != 1:
    raise SystemExit("expected exactly one keywords block in paper/main.tex")
body = source.split(r"\keywords{", 1)[1]
body = r"\keywords{" + body
body = re.sub(r"\\pagestyle\{overlapreview\}\s*", "", body, count=1)
if r"\begin{document}" in body or r"\title[" in body or r"\author{" in body:
    raise SystemExit("unexpected title/byline material in retained manuscript body")

for forbidden in ("\\ACM@linecount", "\\fancypagestyle{overlapreview}", "\\acmConference", "\\setcopyright"):
    if forbidden in body:
        raise SystemExit(f"review/ACM furniture unexpectedly present in body: {forbidden}")

class_line = r"\documentclass[sigplan,10pt,nonacm,screen]{acmart}"
preamble = source.split(r"\begin{document}", 1)[0]
preamble, n = re.subn(r"(?m)^\\documentclass\[[^\]]*\]\{acmart\}\s*", lambda _: class_line + "\n", preamble, count=1)
if n != 1:
    raise SystemExit("could not replace the ACM conference class declaration")
preamble = re.sub(r"(?m)^\\usepackage\[safe\]\{pbalance\}\s*$\n?", "", preamble)
preamble = re.sub(r"(?m)^\\setcopyright\{[^\n]*\}\s*$\n?", "", preamble)
preamble = re.sub(r"(?m)^\\acm(?:Conference|Booktitle|DOI|ISBN)\b[^\n]*\s*$\n?", "", preamble)
preamble = re.sub(r"(?m)^\\renewcommand\\footnotetextcopyrightpermission\[1\]\{\}\s*$\n?", "", preamble)
preamble = re.sub(
    r"\\makeatletter\s*% Keep acmart review line numbers.*?\\makeatother\s*",
    "",
    preamble,
    count=1,
    flags=re.S,
)
preamble = "\n".join((r"\pdfoutput=1", r"\PassOptionsToClass{balance=false}{acmart}", preamble))
if any(token in preamble for token in ("review", "anonymous", "\\acmConference", "\\fancypagestyle")):
    raise SystemExit("review or ACM conference furniture remains in export preamble")
preamble += r"\IfPackageLoadedTF{hyperxmp}{\hypersetup{keeppdfinfo}}{}" + "\n"
preamble += r"\begin{document}" + "\n"
title = fields["Title"]
abstract = fields["Abstract"]
title_block = (
    "\\title{" + title + "}\n"
    "\\author{" + author_name + "}\n"
    "\\orcid{" + orcid_id + "}\n"
    "\\affiliation{\\institution{" + affiliation + "}\\city{}\\country{}}\n"
    "\\email{" + email + "}\n"
    "\\authornote{Website: \\url{" + website + "}}\n"
    "\\begin{abstract}\n" + abstract + "\n\\end{abstract}\n"
)
artifact = (
    "\\paragraph{Availability.} The proof and source are available at "
    "\\url{https://github.com/Hallllllll/erdos36-minimum-overlap-lean4}. "
    "The v1.0.0 witness is archived at \\href{https://doi.org/10.5281/zenodo.24575270}{10.5281/zenodo.24575270}.\n"
)
if body.count(r"\maketitle") != 1:
    raise SystemExit("expected exactly one existing \\maketitle in the manuscript body")
body = body.replace(r"\maketitle", r"\maketitle" + "\n" + artifact, 1)
generated = preamble + title_block + body
output_path.write_text(generated, encoding="utf-8")

human = r"\section*{Human Contributions and AI Assistance}"
if source.count(human) != 1 or generated.count(human) != 1:
    raise SystemExit("Human Contributions section was not preserved exactly once")
start = source.index(human)
end = source.index(r"\bibliographystyle", start)
original_section = source[start:end]
gstart = generated.index(human)
gend = generated.index(r"\bibliographystyle", gstart)
if original_section != generated[gstart:gend]:
    raise SystemExit("Human Contributions section changed during export")
PY

# These are the transitive project inputs; acmart and PGFPlots come from TeX Live.
inputs=(
  related.tex generated/metrics.tex generated/witness-profile.pdf
  figures/packing.tex figures/bridge.tex figures/linux-scaling.tex figures/platforms.tex
  validation/linux-censored.dat validation/linux-direct-elaboration.dat
  validation/linux-direct-replay.dat validation/linux-packed-elaboration.dat
  validation/linux-packed-replay.dat
)
for file in "${inputs[@]}"; do
  install -d "$SOURCE_DIR/$(dirname "$file")"
  install -m 644 "$PAPER_DIR/$file" "$SOURCE_DIR/$file"
done

# BibTeX runs only during export. It is intentionally absent from the submission.
cp "$PAPER_DIR/references.bib" "$INITIAL_BUILD/"
cd "$SOURCE_DIR"
pdflatex -halt-on-error -interaction=nonstopmode -output-directory="$INITIAL_BUILD" main.tex > "$TMP_ROOT/bibliography-pass.log" || { tail -30 "$TMP_ROOT/bibliography-pass.log"; exit 1; }
(cd "$INITIAL_BUILD" && bibtex main)
cp "$INITIAL_BUILD/main.bbl" "$SOURCE_DIR/main.bbl"
members=(main.tex main.bbl "${inputs[@]}")
archive="$TMP_ROOT/arxiv-submission.tar.gz"

# Normalize the archive headers and gzip timestamp so equal sources pack identically.
"$PYTHON_BIN" - "$archive" "${members[@]}" <<'PY'
import gzip
from pathlib import Path
import sys
import tarfile

with open(sys.argv[1], "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
    with tarfile.open(fileobj=gz, mode="w", format=tarfile.USTAR_FORMAT) as archive:
        for name in sorted(sys.argv[2:]):
            path = Path(name)
            entry = tarfile.TarInfo(name)
            entry.size = path.stat().st_size
            entry.mode = 0o644
            with path.open("rb") as source:
                archive.addfile(entry, source)
PY

cd "$EXTRACT_DIR"
tar -xzf "$archive"
for pass in 1 2; do
  pdflatex -interaction=nonstopmode main.tex > "$TMP_ROOT/pass-$pass.log" || {
    tail -30 "$TMP_ROOT/pass-$pass.log" >&2
    exit 1
  }
done
if rg -an 'Overfull .*box|undefined references|(?:Citation|Reference).*undefined|Package balance Warning' main.log; then
  exit 1
fi

mkdir -p "$(dirname "$ARXIV_OUTPUT_DIR")"
RENDER_DIR="$(mktemp -d "${ARXIV_OUTPUT_DIR}.XXXXXX")"
cp main.pdf "$RENDER_DIR/arxiv-submission.pdf"
cp main.log "$RENDER_DIR/main.log"
pdftoppm -png -r 120 main.pdf "$RENDER_DIR/page"
pages="$(pdfinfo main.pdf | awk '/^Pages:/ {print $2}')"
echo "Clean-room build: $pages pages; preview, PNGs and final TeX log in $RENDER_DIR"

# Publish only the verified inputs, leaving the hand-edited submission sheet intact.
for file in "${members[@]}"; do
  install -d "$ARXIV_DIR/$(dirname "$file")"
  install -m 644 "$EXTRACT_DIR/$file" "$ARXIV_DIR/$file"
done
install -m 644 "$archive" "$ARXIV_DIR/arxiv-submission.tar.gz"
echo "Upload $ARXIV_DIR/arxiv-submission.tar.gz"
