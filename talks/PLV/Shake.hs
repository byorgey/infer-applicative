#!/usr/bin/env stack
-- stack --resolver lts-22.33 script --package shake

import Development.Shake
import Development.Shake.FilePath

lhs2TeX, pdflatex, latexmk :: String
lhs2TeX = "lhs2TeX"
pdflatex = "pdflatex"
latexmk = "latexmk"

main :: IO ()
main = shake shakeOptions $ do
  want ["PLV-idiomatic-inference.pdf"]

  "*.tex" %> \output -> do
    let input = replaceExtension output "lhs"
    need [input]
    cmd lhs2TeX $ ["-o", output] ++ [input]

  "*.pdf" %> \output -> do
    let input = replaceExtension output "tex"
    need [input]

    -- need ["Diagrams.hs"]  -- for document-specific diagrams

    () <- cmd pdflatex $ ["--enable-write18", input]
    cmd "pdflatex" $ [input]
