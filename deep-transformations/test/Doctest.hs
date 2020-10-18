import Build_doctests (flags, pkgs, module_sources)
import Test.DocTest (doctest)

main :: IO ()
main = do
    doctest (flags ++ pkgs ++ module_sources)
    doctest (flags ++ pkgs ++ ["-pgmL", "markdown-unlit", "-isrc", "test/README.lhs"])
    doctest (flags ++ pkgs ++ ["-isrc", "test/RepMin.hs"])
