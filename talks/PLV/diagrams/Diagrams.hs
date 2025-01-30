#!/usr/bin/env stack
-- stack --resolver lts-22.33 script --package diagrams-lib --package diagrams-pgf --package texrunner --package diagrams-contrib --package random

{-# LANGUAGE LambdaCase #-}

import Data.List (transpose, intersperse)
import Diagrams.TwoD.Layout.Tree
import Diagrams.Backend.PGF.CmdLine
import Diagrams.Prelude hiding (Box, Empty)
import System.Random

data Polarity = Pos | Neg deriving (Eq, Ord, Show)

neg :: Polarity -> Polarity
neg Pos = Neg
neg Neg = Pos

polColor :: Polarity -> Colour Double
polColor Pos = white
polColor Neg = black

data BTNode = BTNode !Polarity !Int

type BoxTree = BTree BTNode

box :: BoxTree -> BoxTree
box Empty = Empty
box (BNode (BTNode p n) l r) = BNode (BTNode p (n+1)) l r

infixr 1 :->:

data Ty = Base | Ty :->: Ty | Box Ty | Contra Ty deriving (Eq, Ord, Show)

toBoxTree :: Ty -> BoxTree
toBoxTree = toBoxTree' Pos
  where
    toBoxTree' pol = \case
      Contra ty -> toBoxTree' (neg pol) ty
      Base -> leaf (BTNode pol 0)
      t1 :->: t2 -> BNode (BTNode pol 0) (toBoxTree' (neg pol) t1) (toBoxTree' pol t2)
      Box t -> box (toBoxTree' pol t)

drawBTNode :: BTNode -> Diagram B
drawBTNode (BTNode pol n) =
  cat' unit_X (with & sep .~ 0.05) $
  circle 0.1 # fc (polColor pol) : replicate n (square 0.15)

drawBoxTree :: BoxTree -> Diagram B
drawBoxTree =
  maybe mempty (renderTree drawBTNode (~~)) .
  symmLayoutBin' (with & slVSep .~ 0.5)

drawTy :: Ty -> Diagram B
drawTy = drawBoxTree . toBoxTree

drawChain :: [Ty] -> Diagram B
drawChain = hsep 0.3 . map centerY . intersperse arr . map drawTy
  where
    arr = text "$\\Longrightarrow$" # fontSizeL 0.2

drawRule :: Ty -> Ty -> Diagram B
drawRule t1 t2 = drawChain [t1, t2]

boxRules :: Diagram B
boxRules = vsep 1 . map (hsep 1) . transpose . map (uncurry genRules) $
  [(Base, Box Base), (Box (Base :->: Base), Box Base :->: Box Base)]

genRules :: Ty -> Ty -> [Diagram B]
genRules t1 t2 = [drawRule t1 t2, drawRule (Contra t2) (Contra t1)]

bigTy :: Ty
bigTy = ((Base :->: Base) :->: Base) :->: ((Base :->: Base :->: Base) :->: Base)

sprinkleBoxes :: Ty -> IO Ty
sprinkleBoxes = \case
  Contra t -> Contra <$> sprinkleBoxes t
  Box t -> Box <$> sprinkleBoxes t
  Base -> randomRIO (0,2) >>= \n -> pure (applyBoxes n Base)
  (t1 :->: t2) -> randomRIO (0,2) >>= \n -> applyBoxes n <$> ((:->:) <$> sprinkleBoxes t1 <*> sprinkleBoxes t2)

applyBoxes :: Int -> Ty -> Ty
applyBoxes 0 t = t
applyBoxes n t = Box (applyBoxes (n-1) t)

main = do
  renderPGF "B->B.pgf" (mkWidth 75) (drawTy (Base :->: Base))
  renderPGF "B->xB.pgf" (mkWidth 75) (drawTy (Base :->: Box Base))
  renderPGF "x(B->B).pgf" (mkWidth 75) (drawTy $ Box (Base :->: Base))
  renderPGF "(B->B)->B.pgf" (mkWidth 75) (drawTy $ (Base :->: Base) :->: Base)
  renderPGF "box-rules.pgf" (mkWidth 300) boxRules
  renderPGF "chains.pgf" (mkWidth 400) . vsep 1 . map (centerX . drawChain) $
    [ [ Base :->: Base
      , Box (Base :->: Base)
      , Box Base :->: Box Base
      , Box (Box Base :->: Box Base)
      , Box (Box Base) :->: Box (Box Base)
      , Box Base :->: Box (Box Base)
      ]
    , [ Base :->: Base
      , Base :->: Box Base
      , Box (Base :->: Box Base)
      , Box Base :->: Box (Box Base)
      ]
    ]
  bigTy1 <- sprinkleBoxes bigTy
  bigTy2 <- sprinkleBoxes bigTy
  renderPGF "random.pgf" (mkWidth 400) (hsep 0.5 . map centerY $ [drawTy bigTy1, text "$\\stackrel{?}{\\Longrightarrow}$" # fontSizeL 0.2, drawTy bigTy2])
