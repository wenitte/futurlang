# Executable FuturLang

This file documents the current executable subset used by FuturLang's runtime paths:

- `fl <file.fl>` executes the program and also shows checker output first for proof-shaped files
- `fl start <file.fl>` starts apps: server files run directly, frontend files generate and launch the React/Vite app
- `fl web <file.fl>` generates frontend output without launching it

## Surface

Executable FuturLang is still FuturLang:

- the file is one visible chain
- adjacent top-level constructs still need explicit connectives
- `fn`, `type`, `struct`, `let`, `match`, and runtime assertions all live in the same surface

## Supported Top-Level Constructs

- `import "./other.fl"`
- `fn name(args...) -> Return { ... }`
- `type Name = | Variant(...) ...`
- `struct Name { ... }`
- `let name = value`
- theorem/proof blocks, though executable use is narrower than checker use

Imports are currently expanded textually before parsing.

## Expressions

Supported executable expressions include:

- literals: booleans, numbers, strings
- function calls
- `if cond then a else b`
- `let x = expr in body`
- lambdas: `fn(x: Nat) => x + 1`
- list literals
- `fold(xs, init, f)`
- constructor calls from `type` declarations

## Pattern Matching

Value-level matching works in executable `fn` bodies.

Supported patterns:

- `[]`
- `[x, ...rest]`
- `_`
- variant patterns like `Ok(v)` and `Err(msg)`
- bare boolean cases like `case true`

## Runtime Data

Runtime values currently include:

- lists as JS arrays
- sum-type values as tagged JS objects
- structs as plain objects when created manually in executable code

## Narrow Static Type Checking

Before JS code generation, FuturLang runs a narrow executable type check.

It currently validates:

- function argument/return compatibility
- simple constructor usage
- `if` condition type
- list element flow
- some `fold` and handler signatures

It is intentionally incomplete and should be treated as an early guardrail, not a full type system.

## Node HTTP Helpers

The runtime includes a small Node `http` wrapper.

### Requests and Responses

- `request("GET", "/users")`
- `text("hello")`
- `html("<h1>hi</h1>")`
- `json(Ok(7))`

### Routing

- `route("GET", "/", handler)`
- `router([route(...), route(...)])`
- `dispatch(app, request("GET", "/"))`

### Serving

- `serve(3000, app)`
- `serve(3000, app, "0.0.0.0")`

Example:

```fl
type ApiResult =
  | Ok(value ∈ Nat)
  | Err(message ∈ String)
} →

fn home(req ∈ Request) -> Response {
  conclude(text("home"))
} →

fn api(req ∈ Request) -> Response {
  conclude(json(Ok(7)))
} →

let app = router([
  route("GET", "/", home),
  route("GET", "/api", api)
]) →
let server = serve(3000, app)
```

Run it with:

```bash
fl start examples/server/hello-http.fl
```

or simply:

```bash
fl examples/server/hello-http.fl
```

## Current Boundary

The executable subset is still narrower than the checker surface.

Notably incomplete today:

- robust module/export semantics beyond textual import expansion
- broad inline-lambda support in every nested expression shape
- exhaustive typed field/record support
- full effect typing
- source-mapped runtime diagnostics
