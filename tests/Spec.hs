import Test.Hspec

import qualified ExecTests
import qualified FunctTests

main :: IO ()
main = do
    execTests <- ExecTests.spec
    functTests <- FunctTests.spec
    hspec execTests
    hspec functTests
