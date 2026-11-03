module Tests.ProjectNew

import Data.IORef
import Data.List
import Data.String
import Fibril.Project.Template
import Fibril.Project.New
import Fibril.Project.Manifest

%default total

record Attempt where
  constructor Attempted
  result : Either String ()
  calls : List String

simulateOwned : Nat -> String -> Maybe String -> IO Attempt
simulateOwned failAt name owned = do
  seen <- newIORef (the (List String) [])
  let operation : String -> IO (Either String ()) = \label => do
        before <- readIORef seen
        modifyIORef seen (label ::)
        pure (if length before == failAt then Left "Injected creation/write/close failure" else Right ())
  result <- createPackageWith (CreatingWith (\path => operation ("directory " ++ path))
                       (\path, contents => operation ("file " ++ path))) name owned
  calls <- readIORef seen
  pure (Attempted result (reverse calls))

simulate : Nat -> String -> IO Attempt
simulate failAt name = simulateOwned failAt name Nothing

simulateLibrary : Nat -> String -> IO Attempt
simulateLibrary failAt owned = do
  seen <- newIORef (the (List String) [])
  let operation : String -> IO (Either String ()) = \label => do
        before <- readIORef seen
        modifyIORef seen (label ::)
        pure (if length before == failAt then Left "Injected library failure" else Right ())
  result <- createLibraryWith (CreatingWith (\path => operation ("directory " ++ path))
                        (\path, contents => operation ("file " ++ path))) "mailer" owned
  calls <- readIORef seen
  pure (Attempted result (reverse calls))

failed : Either String () -> Bool
failed (Left _) = True
failed _ = False

partialReported : Either String () -> Bool
partialReported (Left message) = isInfixOf "Partial project may remain" message && isInfixOf "no rollback" message
partialReported _ = False

public export
runProjectChecks : IO (List (String, Bool))
runProjectChecks = do
  libraryTooLong <- simulateLibrary 99 (pack (replicate 1019 'A'))
  librarySuccess <- simulateLibrary 99 "Email.Core"
  libraryFailures <- traverse (\index => simulateLibrary index "Email.Core") [0,1,2,3,4,5,6,7,8]
  tooLong <- simulateOwned 99 "mailer" (Just (pack (replicate 1025 'A')))
  invalidPrefix <- simulateOwned 99 "mailer" (Just "Main.Core")
  packageSuccess <- simulateOwned 99 "mailer" (Just "Mailer.Core")
  manifestFailure <- simulateOwned 7 "mailer" (Just "Mailer.Core")
  appFailures <- traverse (\index => simulateOwned index "mailer" (Just "Mailer.Core")) [0,1,2,3,4,5,6,7,8]
  appTooLong <- simulateOwned 99 "mailer" (Just (pack (replicate 1019 'A')))
  invalid <- simulate 99 "../escape"
  admission <- simulate 0 "mailer"
  directory <- simulate 1 "mailer"
  firstFile <- simulate 2 "mailer"
  laterFile <- simulate 4 "mailer"
  success <- simulate 99 "mailer"
  pure
    [ ("library derived namespace admission and pure manifest roundtrip",
        validLibraryPrefix (pack (replicate 1018 'A')) && not (validLibraryPrefix (pack (replicate 1019 'A'))) &&
        failed libraryTooLong.result && null libraryTooLong.calls &&
        (case find (\file => file.path == "fibril.yaml") (libraryFiles "mailer" (pack (replicate 1018 'A'))) of
          Just file => case decodeManifest "fibril.yaml" file.contents of Right manifest => manifest.entry == Nothing && length manifest.listedModules == 1; _ => False
          _ => False))
    , ("app derived test namespace roundtrips at scalar admission boundary",
        validTestedPrefix (pack (replicate 1018 'A')) && not (validTestedPrefix (pack (replicate 1019 'A'))) &&
        (case find (\file => file.path == "fibril.yaml") (packageFiles "mailer" (pack (replicate 1018 'A'))) of
          Just file => case decodeManifest "fibril.yaml" file.contents of Right manifest => manifest.entry == Just "Main" && manifest.testModule /= Nothing; _ => False
          _ => False))
    , ("library creation is parent-first and stops on every represented failure",
        (case librarySuccess.result of Right () => True; _ => False) &&
        librarySuccess.calls == ["directory mailer", "directory mailer/src", "directory mailer/src/Email", "directory mailer/src/Email/Core", "file mailer/src/Email/Core.fib", "file mailer/src/Email/Core/Tests.fib", "file mailer/.gitignore", "file mailer/fibril.yaml", "file mailer/README.md"] &&
        all (\(index, attempt) => failed attempt.result && length attempt.calls == S index &&
          (index == 0 || partialReported attempt.result)) (zip [0,1,2,3,4,5,6,7,8] libraryFailures))
    , ("explicit namespace profile rejects reserved/malformed owners before effects",
        failed invalidPrefix.result && null invalidPrefix.calls && failed tooLong.result && null tooLong.calls &&
        all (not . validProjectPrefix) ["", "Main", "Main.Core", "lower", "A..B", "A/B", "A\n"] &&
        all validProjectPrefix ["Mailer", "Email.Core", "MainView", pack (replicate 1024 'A')] &&
        not (validProjectPrefix (pack (replicate 1025 'A'))))
    , ("package creation uses fixed exclusive manifest path and stops on manifest failure",
        (case packageSuccess.result of Right () => True; _ => False) &&
        packageSuccess.calls == ["directory mailer", "directory mailer/src", "directory mailer/src/Mailer", "directory mailer/src/Mailer/Core", "file mailer/src/Main.fib", "file mailer/.gitignore", "file mailer/src/Mailer/Core/Tests.fib", "file mailer/fibril.yaml", "file mailer/README.md"] &&
        partialReported manifestFailure.result && length manifestFailure.calls == 8 &&
        failed appTooLong.result && null appTooLong.calls &&
        all (\(index, attempt) => failed attempt.result && length attempt.calls == S index &&
          (index == 0 || partialReported attempt.result)) (zip [0,1,2,3,4,5,6,7,8] appFailures))
    , ("project names reject paths/options/controls and code injection",
        all (not . validProjectName) ["", "..", "../x", "a/b", "a\\b", "-x", "_x", "A", "a b", "a\n", "a\"", pack (replicate 65 'a')])
    , ("valid project directory slugs do not dictate module identity",
        all validProjectName ["mailer", "hello_world", "hello-world", "app2", pack (replicate 64 'a')])
    , ("POSIX runtime identifiers include Chez Unix and RefC names",
        all supportedHost ["unix", "darwin", "Linux", "macOS"] &&
        all (not . supportedHost) ["windows", "mingw32", "cygwin32", "unknown"])
    , ("invalid names produce no creation effects", failed invalid.result && null invalid.calls)
    , ("failed root admission stops before any file writes",
        failed admission.result && admission.calls == ["directory mailer"])
    , ("directory failure reports partial output and stops",
        partialReported directory.result && directory.calls == ["directory mailer", "directory mailer/src"])
    , ("first file failure stops without rollback",
        partialReported firstFile.result && length firstFile.calls == 3)
    , ("later file failure stops and keeps earlier progress",
        partialReported laterFile.result && length laterFile.calls == 5)
    , ("successful creation uses exactly fixed directories/files",
        (case success.result of Right () => True; _ => False) &&
        success.calls == ["directory mailer", "directory mailer/src", "file mailer/src/Main.fib", "file mailer/.gitignore", "file mailer/README.md"])
    ]
