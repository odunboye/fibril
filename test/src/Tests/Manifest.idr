module Tests.Manifest

import Data.List
import Fibril.Project.Manifest
import Fibril.Project.Workspace

%default total

sample : String
sample = "schema: 1\nname: mailer-app\nmodule-prefix: Mailer\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  email-core:\n    path: ../email-core\n"

library : String
library = "schema: 1\nname: email-core\nmodule-prefix: Email.Core\nsource-dir: src\nfoundation: de-morgan\n"

asPackage : String -> PackageManifest -> PackageSpec
asPackage root manifest = LocalPackage manifest.name root manifest.modulePrefix manifest.foundation (map name manifest.dependencies)

public export
checks : List (String, Bool)
checks =
  [ ("maintained YAML decoding yields strict local manifest fields",
      case decodeManifest "fibril.yaml" sample of
        Right spec => spec.name == "mailer-app" && spec.modulePrefix == ["Mailer"] && spec.entry == Just "Main" &&
          map name spec.dependencies == ["email-core"] && map path spec.dependencies == ["../email-core"]
        _ => False)
  , ("two decoded local packages feed the pure ownership planner",
      case (decodeManifest "app/fibril.yaml" sample, decodeManifest "email/fibril.yaml" library) of
        (Right app, Right email) => case planWorkspace [asPackage "/synthetic/app/src" app, asPackage "/synthetic/email/src" email] of
          Right plan => plan.dependencyOrder == ["email-core", "mailer-app"] &&
            (case moduleOwner plan "mailer-app" ["Email", "Core", "Address"] of Right owner => owner.name == "email-core"; _ => False)
          _ => False
        _ => False)
  , ("relative manifest paths do not imply canonicalization or containment",
      relativeManifestPath True "../email-core" && relativeManifestPath True "." &&
      relativeManifestPath False "src/日本 語" && not (relativeManifestPath False "src/../lib") &&
      not (relativeManifestPath False "/src") && not (relativeManifestPath True "C:/mail") &&
      not (relativeManifestPath True "\\\\server\\share") && not (relativeManifestPath True "../bad\n"))
  ]
