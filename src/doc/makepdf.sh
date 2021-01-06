#!/bin/bash
export LC_ALL="en_US.UTF-8"

TEXJOBNAME=tbasman

echo "Making pdfs from dot-graph"
for f in *.dot; do
  echo $f;
  dot -Tpdf -o ${f%.*}.pdf $f;
done

lualatex $TEXJOBNAME.tex
makeindex $TEXJOBNAME
lualatex $TEXJOBNAME.tex
