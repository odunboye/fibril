# Transactional email: standalone application

The email application now lives outside the compiler checkout in the sibling
`../email` project (`/Users/odunadeboye/dev/fibril/src/email` in the development
workspace). The former `/Users/odunadeboye/dev/fibril/email-core` project was moved
there; its `email-core` package name and relative test dependency are preserved.

Application-owned files are:

- `src/App/Delivery.fib`: the eight-state/eight-event pure delivery model.
- `src/App/Request.fib`: pure Enqueue/Preview/Health request labels.
- `demo/src/Main.fib`: a runnable delivery-state simulation.
- `test/src/TestSuite/Suite.fib`: the application's separate Bool tests.
- `docs/production-plan.md`: product decisions, email security requirements and
  the planned relay/API/UI vertical slice.

Those paths are relative to the email project, not the compiler. The compiler's
build, tests and handbook do not require the sibling project to exist. See that
project's README/Makefile to select a compiler checkout and run its check/test/demo.

## Compiler regression fixtures, not application source

Small snapshots remain in this repository solely to test compiler behavior:

- [Submission-only model](../../test/fixtures/modules/email-service/Delivery.fib)
  and [driver](../../test/fixtures/modules/email-service/Main.fib).
- [Full shared-global model](../../test/fixtures/modules/email-service-full/Delivery.fib)
  and [driver](../../test/fixtures/modules/email-service-full/Main.fib).
- [Pure request API](../../test/fixtures/packages/request-api/src/Mail/Request.fib)
  and [package test](../../test/fixtures/packages/request-api/test/src/RequestTests/Main.fib).

Do not develop application features in those snapshots. They are independent,
versioned test inputs; intentional compiler regressions can update them separately.
The generic package/manifest tutorials named `mailer` and `email-core` remain
compiler examples, not copies of the standalone application.

## Runtime boundary and current limits

[Host embedding](../native-embedding.md), [binary embedding](../binary-embedding.md),
[optional SQLite storage](../durable-queue.md) and the
[generic enqueue demonstration](../enqueue-worker.md) remain compiler/runtime
infrastructure. They accept opaque jobs, not validated email requests, and are
not connected to the application's delivery model.

The standalone email project remains a pure model/simulation. No authenticated
API, MIME/address validation, SMTP/TLS submission, durable email dispatch, browser
UI or deployed worker is implemented by this move. A queued job is not proof of
relay acceptance or recipient delivery, and uncertain SMTP submission must not
be retried as though exactly-once delivery were available.
