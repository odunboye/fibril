module Tests.Workspace

import Data.List
import Fibril.Project.Workspace
import Fibril.Project.Name

%default total

pkg : String -> String -> List String -> List String -> PackageSpec
pkg name root owned deps = LocalPackage name root owned "de-morgan" deps

core : PackageSpec
core = pkg "core" "/canonical/core/src" ["Core"] []

mail : PackageSpec
mail = pkg "mail" "/canonical/mail/src" ["Mail"] ["core"]

app : PackageSpec
app = pkg "app" "/canonical/app/src" ["App"] ["mail"]

inventory : List PackageSpec
inventory = [app, core, mail]

rejects : List PackageSpec -> Bool
rejects specs = case planWorkspace specs of Left _ => True; Right _ => False

order : List PackageSpec -> List String
order specs = case planWorkspace specs of Right plan => plan.dependencyOrder; Left _ => []

routes : String -> List String -> String -> Bool
routes requester requested expected = case planWorkspace inventory of
  Left _ => False
  Right plan => case moduleOwner plan requester requested of
    Right owner => owner.name == expected
    _ => False

blocked : String -> List String -> Bool
blocked requester requested = case planWorkspace inventory of
  Left _ => False
  Right plan => case moduleOwner plan requester requested of Left _ => True; _ => False

public export
checks : List (String, Bool)
checks =
  [ ("workspace order is dependency-first and independent of inventory order",
      all (\specs => order specs == ["core", "mail", "app"])
        [inventory, reverse inventory, [mail, app, core], [core, app, mail]])
  , ("workspace ties choose the smallest ready package name",
      order [app, mail, pkg "alpha" "/canonical/alpha/src" ["Alpha"] [], core] == ["alpha", "core", "mail", "app"])
  , ("newly ready packages compete lexically with already ready ones",
      order [pkg "c" "/c" ["C"] [], pkg "b" "/b" ["B"] ["a"], pkg "a" "/a" ["A"] []] == ["a", "b", "c"])
  , ("empty inventory is explicitly rejected", rejects [])
  , ("empty source roots reject without guessing a directory", rejects [pkg "empty" "" ["Empty"] []])
  , ("package names are explicit bounded keys, not inferred namespaces",
      validPackageName "mail-core" && not (validPackageName "Mail") &&
      not (rejects [pkg "different-name" "/no/files/needed" ["Arbitrary"] []]))
  , ("duplicate identity is rejected regardless of root",
      rejects [core, core] && rejects [core, pkg "core" "/different/root" ["Other"] []])
  , ("duplicate supplied source roots are rejected",
      rejects [core, pkg "other" core.sourceRoot ["Other"] []])
  , ("root strings preserve spaces and Unicode without filesystem discovery",
      case planWorkspace [pkg "unicode" "/nonexistent/日本 語/src" ["Unicode"] []] of
        Right plan => map sourceRoot plan.inventory == ["/nonexistent/日本 語/src"]
        _ => False)
  , ("different root spellings are not claimed to be canonical or disjoint",
      not (rejects [pkg "one" "/same" ["One"] [], pkg "two" "/alias/../same" ["Two"] []]))
  , ("empty or invalid owned namespaces are rejected",
      all (\owned => rejects [pkg "bad" "/root" owned []])
        [[], [""], ["lower"], ["Bad.Name"], [".."], ["日本"], replicate 17 "Deep"])
  , ("module component profile accepts sixteen components and keyword spelling",
      not (rejects [pkg "deep" "/root" (replicate 16 "Deep") []]) &&
      not (rejects [pkg "text" "/root" ["String"] []]))
  , ("Main entry namespace is not library ownership",
      rejects [pkg "entry" "/root" ["Main"] []] && rejects [pkg "entry" "/root" ["Main", "Library"] []] && blocked "app" ["Main"])
  , ("compiler-looking namespace names grant no special privilege",
      not (rejects [pkg "ordinary" "/root" ["Fibril", "Http"] []]) &&
      not (rejects [pkg "ordinary" "/root" ["Prelude"] []]))
  , ("equal and ancestor namespaces reject in either input order",
      let parent = pkg "parent" "/parent" ["Text"] []
          child = pkg "child" "/child" ["Text", "Nested"] []
       in rejects [parent, child] && rejects [child, parent] &&
          rejects [parent, pkg "equal" "/equal" ["Text"] []])
  , ("ownership uses components rather than string-prefix coincidence",
      not (rejects [pkg "text" "/text" ["Text"] [], pkg "textual" "/textual" ["Textual"] []]) &&
      not (rejects [pkg "left" "/left" ["Text", "Left"] [], pkg "right" "/right" ["Text", "Right"] []]))
  , ("missing, repeated and self dependencies reject before planning",
      rejects [pkg "bad-name" "/root" ["Bad"] ["../bad"]] &&
      rejects [pkg "missing" "/root" ["Missing"] ["absent"]] &&
      rejects [core, pkg "repeat" "/root" ["Repeat"] ["core", "core"]] &&
      rejects [pkg "self" "/root" ["Self"] ["self"]])
  , ("cycles reject even in disconnected workspace members",
      let a = pkg "a" "/a" ["A"] ["b"]
          b = pkg "b" "/b" ["B"] ["a"]
       in rejects [a, b] && rejects (a :: b :: inventory))
  , ("longer cycles cannot yield a partial successful plan",
      rejects [pkg "a" "/a" ["A"] ["b"], pkg "b" "/b" ["B"] ["c"], pkg "c" "/c" ["C"] ["a"]])
  , ("diamond dependency reuse is not a duplicate package",
      let ui = pkg "ui" "/ui" ["Ui"] ["core"]
          root = pkg "root" "/root" ["Root"] ["mail", "ui"]
       in order [root, ui, mail, core] == ["core", "mail", "ui", "root"] &&
          order [core, mail, ui, { dependencies := ["ui", "mail"] } root] == ["core", "mail", "ui", "root"])
  , ("foundation metadata rejects unsupported or mixed policies",
      rejects [core, { foundation := "other" } app] && rejects [{ foundation := "" } core])
  , ("routing accepts own and explicit direct dependencies",
      routes "app" ["App", "MainView"] "app" && routes "app" ["Mail", "Queue"] "mail" &&
      routes "mail" ["Core", "Text"] "core")
  , ("routing rejects transitive-only and unrelated owners",
      blocked "app" ["Core", "Text"] && blocked "core" ["Mail", "Queue"])
  , ("unknown requester, owner and malformed requested modules fail closed",
      blocked "unknown" ["Core", "Text"] && blocked "app" ["Absent"] &&
      blocked "app" [] && blocked "app" ["App", ".."] && blocked "app" (replicate 17 "App"))
  , ("valid sixteen-component module ownership routes successfully",
      case planWorkspace [pkg "deep" "/deep" (replicate 16 "Deep") []] of
        Right plan => case moduleOwner plan "deep" (replicate 16 "Deep") of Right owner => owner.name == "deep"; _ => False
        _ => False)
  , ("default package admission accepts sixty-four but not sixty-five",
      let specs = map (\n => pkg ("p" ++ show n) ("/p/" ++ show n) ["P" ++ show n] []) (rangeFromTo 0 63)
       in not (rejects specs) && rejects (pkg "extra" "/extra" ["Extra"] [] :: specs))
  , ("default edge admission accepts 256 but not 257 direct edges",
      let leafNames = map (\n => "l" ++ show n) (rangeFromTo 0 31)
          leaves = map (\n => pkg ("l" ++ show n) ("/l/" ++ show n) ["L" ++ show n] []) (rangeFromTo 0 31)
          clients = map (\n => pkg ("c" ++ show n) ("/c/" ++ show n) ["C" ++ show n] leafNames) (rangeFromTo 0 7)
          extra = pkg "c0" "/c/0" ["C0"] ("c1" :: leafNames)
       in not (rejects (leaves ++ clients)) && rejects (extra :: leaves ++ drop 1 clients))
  , ("ambiguous forged namespace plans do not select the first owner",
      case moduleOwner (PlannedWorkspace [core, pkg "other" "/other" ["Core"] []] []) "core" ["Core"] of Left _ => True; _ => False)
  , ("workspace package and edge admission is explicit",
      (case planWorkspaceWith (WithinWorkspace 2 256) inventory of Left _ => True; _ => False) &&
      (case planWorkspaceWith (WithinWorkspace 3 1) inventory of Left _ => True; _ => False) &&
      (case planWorkspaceWith (WithinWorkspace 3 2) inventory of Right _ => True; _ => False))
  ]
