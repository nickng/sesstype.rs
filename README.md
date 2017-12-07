# sesstype

This is an implementation of Multiparty Session Types in Rust.
The `sesstype` crate contains core data structures and utility functions
to model and manipulate a multiparty session type language.

## Build

The best way to build this library is by Rust's `cargo` package manager.

```
$ cargo build
```

## Usage

See the documentation for details usage.

```
$ cargo doc --open
```

### Quickstart

Given the following source code (with the correct dependencies):

```rust
extern crate sesstype;

fn main() {
    let alice = sesstype::Role::new("Alice"); // Alice role
    let bob = sesstype::Role::new("Bob"); // Bob role

    // Creates an interaction between alice and bob (without message/continuation)
    let g0 = sesstype::global::Type::interaction(&alice, &bob);
    let global_type = sesstype::global::Type::add_message(
        g0,
        sesstype::Message::new("lab"), // Message (with "lab" as label)
        sesstype::global::Type::end(), // Continuation
    );

    let local_type = sesstype::project(&global_type, &bob);
    match local_type {
        Some(l) => {
            println!("Global type G: {}", global_type.to_string());
            println!("Local Type G@Bob: {}", l.to_string());
        }
        None => println!("Cannot project: {}", global_type.to_string()),
    }
}
```

Should give the following output:
```
$ cargo run
Global type G: Alice → Bob:lab().end
Local Type G@Bob: Bob?lab().end
```

### Parsing

Alternative way of using the library is through a simple type language with the
grammar:

#### Common

```
ident   = [A-Za-z][A-Za-z0-9]*
role    = ident
message = ident payload
payload = "()"
        | "(" ident ")"
```

#### Global Types

```
global   = "(" role "->" role ":" interact ")"
         | recur
         | typevar
         | end
interact = sendrecv | "{" sendrecv ("," sendrecv)+ "}"
sendrecv = message "." global
recur    = "*" ident "." global
typevar  = ident
end      = "end"
```

#### Local Types

```
local    = role "&" branch
         | role "+" select
         | lrecur
         | ltypevar
         | end
branch   = recv | "{" recv ("," recv)+ "}"
recv     = "?" message "." local
select   = send | "{" send ("," send)+ "}"
send     = "!" message "." local
lrecur   = "*" ident "." local
ltypevar = ident
lend     = "end"
```

### Parsing example:

This program parses an input string, then re-parses the output global type:
```
extern crate sesstype;

let input = String::from("*T . A -> B: { l().T, l2(int).end }");
let global = sesstype::parser::parse_global_type(input.clone());
let parsed = global.unwrap().to_string();
let reparsed = sesstype::parser::parse_global_type(parsed.clone());
print!(
    "Input:\n\t{}\nParsed:\n\t{}\nRe-parsed:\n\t{}\n",
    input,
    parsed,
    reparsed.unwrap().to_string()
)
```

This is one of the expected output (because branches order in interactions are non-deterministic):

```
Input:
	*T . A -> B: { l().T, l2(int).end }
Parsed:
	μT.A → B:{ l().T, l2(int).end }
Re-parsed:
	μT.A → B:{ l().T, l2(int).end }
```

## License

sesstype is licensed under the [Apache License](http://www.apache.org/licenses/LICENSE-2.0).
