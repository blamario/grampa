import Build_doctests (flags, pkgs, module_sources)
import Test.DocTest (doctest)

main = do doctest (flags ++ pkgs ++ module_sources)
          doctest (flags ++ pkgs ++ ["-pgmL", "markdown-unlit", "test/MyModule.lhs"])
