# Compiler regression inputs

The `modules/email-service`, `modules/email-service-full`, and
`packages/request-api` directories were relocated from `examples/` when the real
email project moved to the sibling `../email` application. Their source contents
are unchanged snapshots of compiler regression cases, not application code to
extend here. The compiler's tests and benchmarks use only these local fixtures;
they never load the sibling application's files.

They cover submission transitions, a larger shared-global/native workload, and
qualified imported constructor matching. The independent application's modules
now use its owned `App` namespace and have their own manifest/tests.
