module Latex where

class Latex a where
    latex :: a -> String
    latexsPrec :: Int -> a -> ShowS
    latexList :: [a] -> ShowS
    latex a = latexsPrec 0 a ""
    latexsPrec _ = showString . latex
    latexList xs = intercalateS ", " (fmap latex xs)
    {-# MINIMAL latex | latexsPrec #-}

instance Latex a => Latex [a] where
    latex xs = latexList xs ""

intercalateS :: [a] -> [[a]] -> ([a] -> [a])
intercalateS _   []     = ([]++)
intercalateS _   [x]    = (x++)
intercalateS sep (x:xs) = (x++) . (sep ++) . intercalateS sep xs