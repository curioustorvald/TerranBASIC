#!/bin/bash
export LC_ALL="en_US.UTF-8"

TEXJOBNAME=tbasman

echo "Making pdfs from dot-graph"
for f in *.dot; do
  echo $f;
  dot -Tpdf -o ${f%.*}.pdf $f;
done

rm $TEXJOBNAME.idx
rm $TEXJOBNAME.ind
rm $TEXJOBNAME.toc
rm $TEXJOBNAME.ilg
rm $TEXJOBNAME.aux

# we REALLY need triple-compilation here because LaTeX, otherwise 'constants' will point to p.24 when it should be p.26

lualatex $TEXJOBNAME.tex
lualatex $TEXJOBNAME.tex
makeindex $TEXJOBNAME
lualatex $TEXJOBNAME.tex
