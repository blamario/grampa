import Build_doctests
import Test.DocTest (doctest)

main :: IO ()
main = do
    doctest (flags ++ pkgs ++ module_sources)
    doctest (flags_exe_arithmetic ++ pkgs_exe_arithmetic ++ module_sources_exe_arithmetic)
    doctest (flags_exe_boolean_transformations ++ pkgs_exe_boolean_transformations
             ++ module_sources_exe_boolean_transformations)
    doctest (flags ++ pkgs ++ ["-pgmL", "markdown-unlit", "-isrc", "test/README.lhs"])
