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

  "../../ott/applicative_defns.tex" %> \_ -> do
    need ["../../ott/applicative.ott"]
    cmd (Cwd "../../ott") "ott" $ ["-i", "applicative.ott", "-o", "applicative_defns.tex", "-tex_show_meta", "false", "-tex_wrap", "false"]

  "*.tex" %> \output -> do
    let input = replaceExtension output "lhs"
    need [input]
    cmd lhs2TeX $ ["-o", output] ++ [input]

  "*.pdf" %> \output -> do
    let input = replaceExtension output "tex"
    need [input]
    need ["../../ott/applicative_defns.tex"]

    -- need ["Diagrams.hs"]  -- for document-specific diagrams

    () <- cmd pdflatex $ ["--enable-write18", input]
    cmd "pdflatex" $ [input]
