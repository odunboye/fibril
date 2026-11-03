-- Read-only tooling adapter. Manifest inspection does not load dependencies or check programs.
module Fibril.Driver.Manifest

import Data.List
import Fibril.Project.Manifest
import Fibril.Source.File
import Fibril.Driver.JSON

%default total

public export
manifestFile : String -> IO (Either String (List String))
manifestFile path = do
  loaded <- loadSourceWithin 8192 path
  pure $ do
    source <- case loaded of
      Left error => Left (path ++ ": Manifest read: " ++ show error)
      Right source => Right source
    manifest <- case decodeManifest path source of
      Left error => Left (path ++ ": Manifest: " ++ error.message)
      Right manifest => Right manifest
    Right [jsonObject
      [("version", "1"), ("kind", jsonString "manifest-inspection"), ("path", jsonString path),
       ("checked", "false"), ("resolved", "false"), ("locked", "false"),
       ("name", jsonString manifest.name),
       ("module_prefix", jsonString (concat (intersperse "." manifest.modulePrefix))),
       ("source_dir", jsonString manifest.sourceDirectory), ("foundation", jsonString manifest.foundation),
       ("entry", maybe "null" jsonString manifest.entry),
       ("modules", jsonArray (map (jsonString . concat . intersperse ".") manifest.listedModules)),
       ("tests", maybe "null" (jsonString . concat . intersperse ".") manifest.testModule),
       ("test_package", maybe "null" jsonString manifest.testPackagePath),
       ("dependencies", jsonArray (map (\dep => jsonObject [("name", jsonString dep.name), ("path", jsonString dep.path)]) manifest.dependencies))]]
