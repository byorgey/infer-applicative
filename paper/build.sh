#!/bin/sh

lhs2TeX --poly infer-applicative.lhs -o infer-applicative.tex &&\
    pdflatex infer-applicative.tex
