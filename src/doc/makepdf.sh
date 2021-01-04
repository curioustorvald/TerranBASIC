#!/bin/bash
export LC_ALL="en_US.UTF-8"


echo "Making pdfs from dot-graph"
for f in *.dot; do
  echo $f;
  dot -Tpdf -o ${f%.*}.pdf $f;
done

lualatex tbasman.tex
lualatex tbasman.tex
