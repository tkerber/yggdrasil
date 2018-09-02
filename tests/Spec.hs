import Test.Hspec

import qualified ExecTests

main :: IO ()
main = do
    execTests <- ExecTests.spec
    hspec execTests
