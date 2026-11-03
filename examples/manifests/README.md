# Manifest inspection fixtures

Run from the compiler project:

```sh
./build/exec/fibril manifest examples/manifests/mailer/fibril.yaml
./build/exec/fibril manifest examples/manifests/email-core/fibril.yaml
```

These demonstrate strict local schema decoding, not workspace loading or source
checking. The declared src directories deliberately do not exist. The command
reports checked/resolved/locked as false and never traverses dependency paths.
The unit suite separately feeds both decoded manifests to the pure workspace
planner using synthetic roots. The separate [local package example](../../docs/local-packages.md) now exercises
actual multi-root check/run; these fixtures remain inspection-only.
