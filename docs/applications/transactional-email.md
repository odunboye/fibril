# Transactional email: application target and delivery plan

## Use cases and current status

Build a service that accepts authenticated transactional email requests, durably
queues them, submits them to a relay on another server, and shows delivery events
in a responsive dashboard. Reuse the web UI on mobile through a native bridge
when actual device APIs are needed.

**Implemented now:** a checked pure Fibril relay-submission state model in
[Delivery](../../examples/modules/email-service/Delivery.fib), with a
[runnable demonstration](../../examples/modules/email-service/Main.fib).
It prints sending, accepted by relay, submission unknown, and transition rejected.
It has no network, database, authentication or deployed UI. An [experimental C emitter](../native-c.md) supports a small console subset, not this complete application.
A separate [pure request API](../../examples/packages/request-api/src/Mail/Request.fib)
now exercises direct local matching over Enqueue, Preview and Health; its
[separate test package](../../examples/packages/request-api/test/src/RequestTests/Main.fib)
also matches those constructors through a checked qualified import. Run
`fibril test --package examples/packages/request-api/fibril.yaml`. This is a
request-label model only: it does not validate addresses, accept HTTP, enqueue,
preview messages, submit SMTP or authorize users.

The model's first slice has four states (Queued, Sending, AcceptedByRelay,
SubmissionUnknown) and three events (Dispatch, RelayAccepted,
AcknowledgementLost). It rejects further dispatch from SubmissionUnknown.
Transition functions consume each status/event once. This is not a proof of the
complete mail protocol or of the authenticity of incoming events.

A larger state/event model hit current expanded-core admission. We did not raise
the limit to hide that issue. Shared global references and bounded checking of
non-inlined programs are application prerequisites. The reduced model is only
submission handling, not the entire proposed lifecycle below.

Use a hosted mail provider directly if you only need to send a few messages and
do not need a separate gateway, queue, audit workflow or administrative UI.
Building a service brings security, abuse prevention, deliverability and operations
responsibilities that a type system cannot discharge alone.

![Email-service target and current model](../diagrams/email-service.svg)

Dashed components are not implemented; the solid model is a checked pure
prototype, not a deployed worker.

## Confirmed product decisions

- The remote relay is Postfix; use SMTP submission, not an added HTTPS relay API.
- Deployment is container-based. Organization tenancy and single-/multi-node
  topology still need to be specified; a container is not a tenancy decision.
- The UI must be authored in Fibril and built by Fibril. A separately handwritten
  TypeScript application is not an acceptable substitute.
- JavaScript is the proposed browser execution output; TypeScript declarations
  can be optional interop artifacts, not the UI's source language or a proof step.

Recommended Postfix connection: authenticated port 587 with STARTTLS mandatory,
certificate/hostname verification and no downgrade. If the relay already offers
implicit TLS on port 465, that is also suitable. Confirm its actual listener and
authentication configuration before integration; do not assume port 25 is an
appropriate authenticated application relay.

## Two deployables and a trusted runtime boundary

~~~text
Server-to-server clients -- authenticated HTTPS --> API
Browser / mobile UI ---- authenticated HTTPS --> admin API
                                                    |
                                             transactional outbox
                                                    |
                                               relay worker
                                                    |
                                      mandatory TLS --> remote relay
                                                    |
                                  authenticated events / reconciliation
~~~

Container server target: Fibril domain code compiled to C, linked with a small
explicit runtime/adapter boundary. Experimental C emission exists only for a
console subset; the application and its service adapters cannot yet be emitted.
Do not describe a different handwritten service as Fibril-generated C.

Recommended initial native dependencies to evaluate: libcurl for outbound SMTP/
HTTPS and SQLite for a single-node durable queue. Use a maintained HTTP server
adapter and a maintained TLS reverse proxy rather than handwritten HTTP/TLS.
Final HTTP/MIME adapters, license constraints and runtime memory policy are
implementation decisions, not selected guarantees. A multi-node deployment would
need a suitable shared queue/database and lease model instead of assuming SQLite
is a distributed queue.

Required UI path: Fibril application and event-handler source -> independently
checked core -> browser JavaScript plus HTML/CSS assets. Start as a responsive
web/PWA build; use Capacitor when identified mobile SDK access is required.
Capacitor is a practical initial bridge for shared web/mobile assets; specific
SDK/plugin support must be confirmed, not assumed. Build configuration, the DOM
runtime and native SDK bindings are explicit platform adapters, not places to
hide a separately authored TypeScript application.

The first browser milestone must run an interactive Fibril-authored component:
compile actual functions/state/event handling, update a real DOM view on an event,
and validate foreign input before typed use. Printing precomputed markup or
embedding a handwritten JavaScript application is not a Fibril UI backend.
General recursive UI trees, scheduling, listener cleanup and mobile bindings
need explicit follow-up contracts; this pipeline is not implemented yet.

## First real vertical slice

1. Authenticate a server client and authorize its verified sender.
2. Accept one recipient, text and optional HTML, with an idempotency key.
3. Commit a durable message/outbox record before returning accepted/queued.
4. A worker claims a bounded lease, submits through mandatory verified TLS and
   records the relay result without logging message contents or credentials.
5. The dashboard lists status and a per-attempt timeline; it never calls the
   relay directly or embeds relay credentials.
6. Integration tests use a controlled relay and exercise disconnect/crash cases.

Suggested API contract, to formalize after relay/auth choices:

- POST /v1/messages: service authentication + Idempotency-Key, returns a message
  identifier and queued status, not a claim of recipient delivery.
- GET /v1/messages/{id}: authorized status/attempt information.
- An authenticated relay-event endpoint only if the relay offers suitable signed
  events; an arbitrary public callback must not be allowed to mark mail delivered.

Initial scope excludes attachments, bulk campaigns and a public arbitrary-sender
relay. Request/recipient/body limits, quotas and retention must be explicit
application policies. Do not silently accept an unbounded MIME document.

## Delivery semantics: do not promise exactly once

The complete planned lifecycle adds Deferred, Failed, Delivered and Bounced.
Only Queued dispatches normally; known temporary failures may defer with bounded
backoff/jitter, attempt limits and expiry. Permanent failures stop. A relay's
acceptance is not proof that a recipient received or read the message.

If a relay accepts DATA but its acknowledgement is lost, the worker cannot infer
whether resubmission will duplicate delivery. Record SubmissionUnknown and apply
an explicit reconciliation/operator policy. Do not blindly retry it or call the
system exactly-once SMTP delivery. A relay HTTP API with a durable idempotency
contract could improve submission semantics; that depends on the actual relay.

Enqueue idempotency must be tenant/client-scoped and durable: the same key with a
different request body is a conflict, not a second message or a silent overwrite.
Database transactions, worker lease fencing/generations and crash recovery must
be specified and tested. The pure model does not currently implement these.

## Security requirements

- Require authenticated, authorized callers and verified sending identities;
  enforce quotas/rate limits so this cannot become an open relay.
- HTTPS ingress, mandatory verified relay TLS, hostname/CA validation, explicit
  timeouts and no insecure fallback. If SMTP STARTTLS is selected, require it;
  opportunistic plaintext fallback is not acceptable.
- Use maintained cryptographic libraries. No handwritten encryption, TLS,
  certificate bypass or invented password hashing.
- Relay credentials and service signing keys stay server-side in runtime secret
  storage, not source, generated C, logs, browser bundles or mobile binaries.
- Parse/validate addresses and headers; reject CR/LF header injection. Use a real
  MIME/encoding library. Escape template variables according to context.
- Sandbox HTML previews with a restrictive CSP; do not execute email content as
  dashboard JavaScript. Body/attachment storage needs explicit encryption-at-rest,
  access and retention policies; HTTPS does not provide storage encryption.
- Admin sessions need appropriate secure cookies/CSRF controls or a documented
  token protocol; authorize every message/event read. Service API keys are not
  browser login credentials. Multi-tenant isolation requires separate design/tests.
- Signed relay events need verification and replay protection. Configure SPF,
  DKIM, DMARC and bounce/suppression policies at the relay/provider boundary.
- Mobile login should use a suitable native/OAuth flow and OS-backed credential
  storage. Ship trusted web assets, restrict navigation/origins and expose only
  required audited plugins; untrusted remote content must not gain a native bridge.

## UI scope and acceptance

Design a polished, accessible delivery console: clear status badges, searchable
message list, attempt timeline, sender configuration and a safe test-send flow.
Include loading, empty, validation, retryable-error and permission-denied states,
keyboard navigation, readable small screens and a coherent light/dark theme.
Mocks must be visibly marked and cannot imply that a send succeeded.

Start with browser deployment. Add mobile packaging only for identified APIs
such as notifications or a device share sheet; do not request broad SDK permissions
by default. Server-side delivery must not depend on unreliable mobile background
execution.

## Language/runtime blockers and assurance

- Direct data cases, practical implicit elaboration and recursion/collections.
- Shared checked globals so ordinary application models do not expand repeatedly.
- Extend the experimental C backend to the application and establish reproducible build/deployment/runtime contracts.
- Explicit native ABI, ownership/lifetimes, buffers/strings, allocation/failure and
  cancellation policies; narrow fallible network/storage adapters.
- Foreign input validation before bytes/JSON become typed application values.
- JavaScript emission plus typed browser/DOM/event interoperability for the
  required Fibril-authored UI; native SDK bridge ownership/input validation.

Generated C is not automatically memory safe. Quantities alone do not establish
correct allocation, freeing, lifetimes or FFI implementations. Separate compiler
subset claims from the trusted C runtime and third-party libraries. Require
negative tests, sanitizers/fuzzing, static analysis and adapter review; these are
valuable evidence, not a formal whole-service memory-safety/security theorem.

No hard-real-time or deadline guarantee is proposed for an Internet email service.
Network delivery has external uncertainty. Timeouts, bounded queues and latency
SLOs are operational policies, not WCET or schedulability proofs.

## Work lanes and decisions needed

Independent lanes can develop the UI contract/design, domain/protocol tests,
backend/runtime and relay/storage adapters in isolated worktrees. Shared kernel,
ABI and protocol changes require integration gates; no lane may bypass checking
or silently change delivery semantics to demonstrate progress.

Before real integration, still confirm the Postfix submission listener/TLS/auth
policy, container host/architecture, tenancy and required mobile SDKs. Postfix
SMTP does not imply a signed HTTP delivery-event API. Start with relay acceptance
and explicit uncertain-submission handling; authenticated bounce/log/event
correlation is a separate adapter. Neither a relay acknowledgement nor a remote
MTA's acceptance proves inbox placement or reading.

Next application-enabling compiler milestone: a real Fibril-generated interactive
browser slice. Native C/runtime work and protocol/storage contracts can develop
alongside it, without silently replacing either deployable with another language.

No credentials are needed in chat or committed files. The existing separate
application workspace has not been modified by this prototype.
