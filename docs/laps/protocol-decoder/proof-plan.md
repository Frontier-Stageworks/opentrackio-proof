# Proof Plan — protocol-decoder (Slice 4C)

## `ProtocolInfo`

A plain struct holding the decoded name and version:

```lean
structure ProtocolInfo where
  name    : String
  version : ProtocolVersion
```

No `ValidProtocolInfo` predicate needed; the only invariant of interest is
`ValidVersion`, carried by the `version` field.

## `decodeProtocol`

Pattern: `.object _` → look up `"name"` → check `.string` → look up `"version"`
→ delegate to `decodeVersionValue` via `do`.

```lean
def decodeProtocol (j : JsonValue) : Except DecodeError ProtocolInfo :=
  match j with
  | .object _ =>
    match j.lookup? "name" with
    | none    => .error (.missingField "name")
    | some nj =>
      match nj with
      | .string n =>
        match j.lookup? "version" with
        | none    => .error (.missingField "version")
        | some vj => do
            let v ← decodeVersionValue vj
            return { name := n, version := v }
      | _ => .error .expectedString
  | _ => .error .expectedObject
```

Error coverage:
- Non-object input → `expectedObject`
- Missing `"name"` → `missingField "name"`
- `"name"` not a string → `expectedString`
- Missing `"version"` → `missingField "version"`
- `"version"` fails digit/length/type checks → propagated from `decodeVersionValue`

## `decodeProtocol_sound`

```lean
theorem decodeProtocol_sound
    (j : JsonValue) (p : ProtocolInfo)
    (_h : decodeProtocol j = .ok p) :
    ValidVersion p.version :=
  protocolVersion_valid p.version
```

Hard step: none. `protocolVersion_valid` already proved in Slice 4A covers all
`ProtocolVersion` values regardless of how they were constructed.

Automation budget: none needed.
