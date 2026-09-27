-- ai-disclosure: ai-generated

-- The Haskell extraction as a filter, with the interface of
-- test/convert.ml:
--
--   djotv            djot on stdin, HTML on stdout
--   djotv --batch    a framed batch, as test/parsers.ml writes it
--
-- Built with -DBYTESTRING when the extraction maps strings to
-- ByteString; otherwise they are String.

{-# LANGUAGE CPP #-}
module Main (main) where

import qualified Data.ByteString.Char8 as B
import System.Environment (getArgs)
import qualified Html

convert :: B.ByteString -> B.ByteString
#ifdef BYTESTRING
convert = Html.convert
#else
convert = B.pack . Html.convert . B.unpack
#endif

-- For each document, "<byte-length>\n" then that many bytes.
frame :: [B.ByteString] -> B.ByteString
frame = B.concat . concatMap (\d -> [B.pack (show (B.length d)), B.pack "\n", d])

unframe :: B.ByteString -> [B.ByteString]
unframe s = case B.readInt s of
  Just (n, rest) ->
    let body = B.drop 1 rest in B.take n body : unframe (B.drop n body)
  Nothing -> []

main :: IO ()
main = do
  args <- getArgs
  input <- B.getContents
  B.putStr (case args of
    ["--batch"] -> frame (map convert (unframe input))
    _ -> convert input)
