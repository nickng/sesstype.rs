// Copyright 2017 The libsesstype Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![crate_type = "lib"]
#![crate_name = "sesstype"]

//! The sesstype crate provides a representation of (multiparty) session types
//! and utilities to construct and manipulate session types in Rust.
//!
//! For a background of *Multiparty Session Types* (MPST),
//! see [Multiparty Asynchronous Session Types]
//! (https://dl.acm.org/citation.cfm?id=2827695) by Honda, Yoshida and Carbone.
//! This implementation of MPST closely follow the syntax defined in
//! [A Linear Decomposition of Multiparty Sessions for Safe Distributed Programming]
//! (http://mrg.doc.ic.ac.uk/publications/a-linear-decomposition-of-multiparty-sessions-for-safe-distributed-programming/)
//! by Scalas et al.

#[macro_use]
extern crate nom;

/// The module provides parser for a simple session type language.
///
/// # Grammar
///
/// Two parser functions are provided for *Global Type* and *Local Type*
/// respectively, as with the parent `sesstype` module, both types share
/// common elements `role` and `message`, and the grammars are shown below:
///
/// ## Common
///
/// ```ignore
/// ident   = [A-Za-z][A-Za-z0-9]*
/// role    = ident
/// message = ident payload
/// payload = "()"
///         | "(" ident ")"
/// ```
///
/// ## Global Types
///
/// ```ignore
/// global   = "(" role "->" role ":" interact ")"
///          | recur
///          | typevar
///          | end
/// interact = sendrecv | "{" sendrecv ("," sendrecv)+ "}"
/// sendrecv = message "." global
/// recur    = "*" ident "." global
/// typevar  = ident
/// end      = "end"
/// ```
///
/// ## Local Types
///
/// ```ignore
/// local    = role "&" branch
///          | role "+" select
///          | lrecur
///          | ltypevar
///          | end
/// branch   = recv | "{" recv ("," recv)+ "}"
/// recv     = "?" message "." local
/// select   = send | "{" send ("," send)+ "}"
/// send     = "!" message "." local
/// lrecur   = "*" ident "." local
/// ltypevar = ident
/// lend     = "end"
/// ```
///
pub mod parser;

mod projection;

use std::cmp::Eq;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::string::ToString;

pub use projection::project;

/// Payload Type carried by a `Message`.
///
/// A `PayloadType` can be one of:
///
/// - base type: `String` symbol that maps to a data type (e.g. `"bool"`, `"int"`)
/// - closed local type: local session type used for session delegation
///
#[derive(Debug)]
pub enum PayloadType {
    BaseType(String), // String symbol that maps to a base type
    Session(Box<local::Type>), // Closed local type
    Empty,
}

/// A structure to represent a message passed between `Role`s.
///
/// A `Message` consists of a label, and optionally, a `PayloadType`
/// embedded in the `Message`.
/// Note that the *payload types* are not real types but `String`
/// symbols that map to sorts.
///
/// `Message` should never be shared.
///
#[derive(Debug)]
pub struct Message {
    label: String, // label of the message, can be empty
    payload: PayloadType, // (optional) payload types string
}

impl Message {
    /// Creates a new `Message` with the given label.
    ///
    /// The `Message` created by this method will have an empty `PayloadType`.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Message;
    ///
    /// let _msg = Message::new("label"); // label()
    /// ```
    ///
    pub fn new(label: &str) -> Message {
        Message {
            label: String::from(label),
            payload: PayloadType::Empty,
        }
    }

    /// Returns the label of the `Message`.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Message;
    ///
    /// let msg = Message::new("label"); // label()
    /// let _msg_label = msg.label(); // "label"
    /// ```
    ///
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Creates a `Message` with a base type payload.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Message;
    ///
    /// let _msg = Message::with_payload_type("label", "int"); // label(int)
    /// ```
    ///
    pub fn with_payload_type(label: &str, payload: &str) -> Message {
        Message {
            label: String::from(label),
            payload: PayloadType::BaseType(String::from(payload)),
        }
    }

    /// Creates a `Message` with a session type payload.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Message;
    /// use sesstype::local;
    ///
    /// let _msg = Message::with_payload_session("label", local::Type::end()); // label(end)
    /// ```
    ///
    pub fn with_payload_session(label: &str, payload: Box<local::Type>) -> Message {
        Message {
            label: String::from(label),
            payload: PayloadType::Session(payload),
        }
    }
}

impl Clone for Message {
    fn clone(&self) -> Message {
        match self.payload {
            PayloadType::BaseType(ref t) => Message {
                label: self.label.clone(),
                payload: PayloadType::BaseType(t.clone()),
            },
            PayloadType::Session(ref s) => Message {
                label: self.label.clone(),
                payload: PayloadType::Session(s.clone()),
            },
            PayloadType::Empty => Message {
                label: self.label.clone(),
                payload: PayloadType::Empty,
            },
        }
    }
}

impl ToString for Message {
    /// Converts `Message` into a human friendly `String` representation.
    ///
    /// The format of the `String` representation is `Label(payload)`
    ///
    fn to_string(&self) -> String {
        let payload = match self.payload {
            PayloadType::BaseType(ref t) => String::from(t.as_str().clone()),
            PayloadType::Session(ref s) => String::from(s.to_string().clone()),
            PayloadType::Empty => String::from(""),
        };

        format!(
            "{label}({payload})",
            label = self.label.clone(),
            payload = payload
        )
    }
}

impl PartialEq for Message {
    fn eq(&self, other: &Message) -> bool {

        self.label == other.label // TODO: payload type comparison.
    }
}

impl Eq for Message {}

impl Hash for Message {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.label.hash(state);
    }
}

/// A participant of a multiparty session.
///
/// The `Role` type represents an endpoint participant of a multiparty
/// session, and the `name` is used for uniquely identifying the
/// participant within the session.
///
/// Typical usage of a `Role` is to create once in a session, and reuse
/// the same `Role` variable in the session.
///
#[derive(Debug)]
pub struct Role {
    name: String,
}

impl Role {
    /// Creates a new `Role` with the given name.
    ///
    /// The `Role` returned is a reference counted pointer variable,
    /// and within the same session, all references to the `Role`
    /// should use the same variable.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Role;
    ///
    /// let _alice = Role::new("Alice");
    /// ```
    ///
    pub fn new(name: &str) -> Rc<Role> {
        Rc::new(Role { name: name.to_string() })
    }

    /// Returns the name of the `Role`.
    ///
    /// # Example
    ///
    /// ```
    /// use sesstype::Role;
    ///
    /// let alice = Role::new("Alice");
    /// let _alice_name = alice.name();
    /// ```
    ///
    pub fn name(&self) -> &String {
        &self.name
    }
}

impl ToString for Role {
    fn to_string(&self) -> String {
        self.name.clone()
    }
}

/// The module provides types and utilities for working with global session types.
///
pub mod global {
    use std::collections::HashMap;
    use std::rc::Rc;

    /// Global session types.
    ///
    /// > Definition 2.17
    /// >
    /// > G ::= p → q : { lᵢ(Uᵢ).Gᵢ } where i ∈ I
    /// >     | μt.G
    /// >     | t
    /// >     | end
    ///
    #[derive(Debug)]
    pub enum Type {
        /// Interaction Type between two `Role`s.
        ///
        /// > G ::= p → q : { lᵢ(Uᵢ).Gᵢ } where i ∈ I
        ///
        /// `p` and `q` are sender and receiver `Role`s respectively, and
        /// `g` is a mapping from `Message` to continuation `Type`.
        ///
        /// Each map entry represents a `Message` sent by `p` to `q`,
        /// then the interaction proceeds as the continuation `Type`.
        ///
        /// The `Message` should be distinct across in this Interaction Type.
        ///
        Interact {
            p: Rc<super::Role>,
            q: Rc<super::Role>,
            g: HashMap<super::Message, Box<Type>>,
        },

        /// Recursive Type for representing infinite behaviour.
        ///
        /// > G ::= μt.G
        ///
        /// `t` is the type variable for identifying the recursion, and
        /// `g` is the `Type` for the continuation.
        ///
        Recur { t: String, g: Box<Type> },

        /// Type Variable for use with `Recur` to represent infinite behaviour.
        ///
        /// > G ::= t
        ///
        /// `t` is the previously defined type variable in `Recur`.
        ///
        TypeVar { t: String },

        /// Terminated Type with no continuation.
        ///
        /// > G ::= end
        ///
        End,
    }

    impl Type {
        /// Returns a heap-allocated `Type::Interact` with no interactions.
        ///
        /// `p` and `q` are the sender and receiver `Role`s respectively.
        ///
        pub fn interaction(p: &Rc<super::Role>, q: &Rc<super::Role>) -> Box<Type> {
            Box::new(Type::Interact {
                p: p.clone(),
                q: q.clone(),
                g: HashMap::new(),
            })
        }

        /// Adds a message `m_i` (and its continuation `g_i`) to a
        /// `Type::Interact` and returns the updated Interact Type.
        ///
        /// `interact_type` is the input `Type`, if it is not a
        /// `Type::Interact` it is returned unmodified.
        ///
        pub fn add_message(
            interact_type: Box<Type>,
            m_i: super::Message,
            g_i: Box<Type>,
        ) -> Box<Type> {
            let mut m_interact_type = interact_type;
            match *m_interact_type {
                Type::Interact { ref mut g, .. } => {
                    g.insert(m_i, g_i);
                    ()
                }
                _ => (),
            }

            m_interact_type
        }

        /// Returns a heap-allocated `Type::Recur`.
        ///
        /// `name` is the name given to the recursion scope.
        /// `body` is the recursion body.
        ///
        pub fn recur(name: &str, body: Box<Type>) -> Box<Type> {
            Box::new(Type::Recur {
                t: String::from(name),
                g: body,
            })
        }

        /// Returns a heap-allocated `Type::TypeVar`.
        ///
        /// `name` is the (previously defined) name of the recursion scope.
        ///
        pub fn typevar(name: &str) -> Box<Type> {
            Box::new(Type::TypeVar { t: String::from(name) })
        }

        /// Returns a heap-allocated `Type::End`.
        ///
        /// All types should end in an instance of this.
        pub fn end() -> Box<Type> {
            Box::new(Type::End)
        }
    }

    impl ToString for Type {
        fn to_string(&self) -> String {
            match *self {
                Type::Interact {
                    ref p,
                    ref q,
                    ref g,
                } => {
                    let mut interact_str = format!("{} → {}:", p.to_string(), q.to_string());
                    match g.len() {
                        1 => {
                            for (m_i, g_i) in g {
                                interact_str.push_str(&format!(
                                    "{}.{}",
                                    m_i.to_string(),
                                    g_i.to_string()
                                ))
                            }
                        }
                        _ => {
                            interact_str.push_str("{ ");
                            let mut first = true;
                            for (m_i, g_i) in g {
                                if !first {
                                    interact_str.push_str(", ")
                                }
                                interact_str.push_str(&format!(
                                    "{}.{}",
                                    m_i.to_string(),
                                    g_i.to_string()
                                ));
                                first = false
                            }
                            interact_str.push_str(" }");
                        }
                    }

                    interact_str
                }
                Type::Recur { ref t, ref g } => format!("μ{}.{}", t, g.to_string()),
                Type::TypeVar { ref t } => format!("{}", t),
                Type::End => String::from("end"),
            }
        }
    }
}

/// The module provides types and utilities for working with local session types.
///
pub mod local {
    use std::collections::HashMap;
    use std::rc::Rc;

    /// Local session types.
    ///
    /// > Definition 2.5
    /// >
    /// > S ::= p &ᵢ ? lᵢ(Uᵢ).Sᵢ where i ∈ I
    /// >     | p ⊕ᵢ ! lᵢ(Uᵢ).Sᵢ where i ∈ I
    /// >     | μt.S
    /// >     | t
    /// >     | end
    ///
    #[derive(Debug)]
    pub enum Type {
        /// Branching Type receives a `Message` chosen by a `Role`.
        ///
        /// > S ::= p &ᵢ ? lᵢ(Uᵢ).Sᵢ where i ∈ I
        ///
        /// `p` is the receiver `Role`, and `s` is the mapping of
        /// `Message` to continuation `Type` choices.
        ///
        /// Each map entry represents a choice received by `q`, where the
        /// key of `s` (a `Message`) is the message expected, and the value
        /// is the continuation `Type` of the Branching Type.
        ///
        Branch {
            p: Rc<super::Role>,
            s: HashMap<super::Message, Box<Type>>,
        },

        /// Selection Type sends a `Message` chosen by a `Role`.
        ///
        /// > S ::= p ⊕ᵢ ! lᵢ(Uᵢ).Sᵢ where i ∈ I
        ///
        /// `p` is the sender `Role`, and `s` is the mapping of
        /// `Message` to continuation `Type` choices.
        ///
        /// Each map entry represents a choice sent by `p`, where the key of
        /// `s` (a `Message`) is the message to send, and the value is the
        /// continuation `Type` of the Selection Type.
        ///
        Select {
            p: Rc<super::Role>,
            s: HashMap<super::Message, Box<Type>>,
        },

        /// Recursive Type for representing infinite behaviour.
        ///
        /// > S ::= μt.S
        ///
        /// `t` is the type variable for identifying the recursion, and
        /// `s` is the `Type` for the continuation.
        ///
        Recur { t: String, s: Box<Type> },

        /// Type Variable for use with `Recur` to represent infinite behaviour.
        ///
        /// > S ::= t
        ///
        /// `t` is the previously defined type variable in `Recur`.
        ///
        TypeVar { t: String },

        /// Terminated Type with no continuation.
        ///
        /// > G ::= end
        ///
        End,
    }

    impl Type {
        /// Returns a heap-allocated `Type::Branch` with no interactions.
        ///
        /// `p` is the receiver `Role`.
        ///
        pub fn branch(p: &Rc<super::Role>) -> Box<Type> {
            Box::new(Type::Branch {
                p: p.clone(),
                s: HashMap::new(),
            })
        }

        /// Returns a heap-allocated `Type::Select` with no interactions.
        ///
        /// `p` is the sender `Role`.
        ///
        pub fn select(p: &Rc<super::Role>) -> Box<Type> {
            Box::new(Type::Select {
                p: p.clone(),
                s: HashMap::new(),
            })
        }

        /// Adds a message `m_i` (and its continuation `s_i`) to a
        /// `Type::Branch` or `Type::Select` and returns the updated
        /// Branch Type or Select Type respectively.
        ///
        /// `selbr_type` is the input `Type`, if it is not a
        /// `Type::Branch` or `Type::Select` it is returned unmodified.
        ///
        pub fn add_message(
            selbr_type: Box<Type>,
            m_i: super::Message,
            s_i: Box<Type>,
        ) -> Box<Type> {
            let mut m_selbr_type = selbr_type;
            match *m_selbr_type {
                Type::Branch { ref mut s, .. } => {
                    s.insert(m_i, s_i);
                    ()
                }
                Type::Select { ref mut s, .. } => {
                    s.insert(m_i, s_i);
                    ()
                }
                _ => (),
            }

            m_selbr_type
        }

        /// Returns the number of branches/selects
        /// for the Type::Branch/Type::Select.
        ///
        /// Returns 1 for other Type variants (1 continuation).
        ///
        pub fn len(&self) -> usize {
            match *self {
                Type::Branch { ref s, .. } => s.len(),
                Type::Select { ref s, .. } => s.len(),
                _ => 1,
            }

        }

        /// Returns a heap-allocated `Type::Recur`.
        ///
        /// `name` is the name given to the recursion scope.
        /// `body` is the recursion body.
        ///
        pub fn recur(name: &str, body: Box<Type>) -> Box<Type> {
            Box::new(Type::Recur {
                t: String::from(name),
                s: body,
            })
        }

        /// Returns a heap-allocated `Type::TypeVar`.
        ///
        /// `name` is the (previously defined) name of the recursion scope.
        ///
        pub fn typevar(name: &str) -> Box<Type> {
            Box::new(Type::TypeVar { t: String::from(name) })
        }

        /// Returns a heap-allocated `Type::End`.
        ///
        /// All types should end in an instance of this.
        pub fn end() -> Box<Type> {
            Box::new(Type::End)
        }
    }

    impl Clone for Box<Type> {
        fn clone(&self) -> Box<Type> {
            match **self {
                Type::Branch { ref p, ref s } => {
                    let mut br = Type::branch(p);
                    for (m_i, s_i) in s {
                        br = Type::add_message(br, m_i.clone(), s_i.clone())
                    }
                    br
                }
                Type::Select { ref p, ref s } => {
                    let mut sel = Type::select(p);
                    for (m_i, s_i) in s {
                        sel = Type::add_message(sel, m_i.clone(), s_i.clone())
                    }
                    sel
                }
                Type::Recur { ref t, ref s } => Type::recur(t, s.clone()),
                Type::TypeVar { ref t } => Type::typevar(&t),
                Type::End => Type::end(),
            }

        }
    }

    impl ToString for Type {
        fn to_string(&self) -> String {
            match *self {
                Type::Branch { ref p, ref s } => {
                    let mut branch_str = format!("{}", p.to_string());
                    match s.len() {
                        1 => {
                            for (m_i, s_i) in s {
                                branch_str.push_str(&format!(
                                    "?{}.{}",
                                    m_i.to_string(),
                                    s_i.to_string()
                                ))
                            }
                        }
                        _ => {
                            branch_str.push_str("&{ ");
                            let mut first = true;
                            for (m_i, s_i) in s {
                                if !first {
                                    branch_str.push_str(", ")
                                }
                                branch_str.push_str(&format!(
                                    "?{}.{}",
                                    m_i.to_string(),
                                    s_i.to_string()
                                ));
                                first = false
                            }
                            branch_str.push_str(" }");
                        }
                    };

                    branch_str
                }
                Type::Select { ref p, ref s } => {
                    let mut select_str = format!("{}", p.to_string());
                    match s.len() {
                        1 => {
                            for (m_i, s_i) in s {
                                select_str.push_str(&format!(
                                    "!{}.{}",
                                    m_i.to_string(),
                                    s_i.to_string()
                                ))
                            }
                        }
                        _ => {
                            select_str.push_str("⊕{ ");
                            let mut first = true;
                            for (m_i, s_i) in s {
                                if !first {
                                    select_str.push_str(", ");
                                }
                                select_str.push_str(&format!(
                                    "!{}.{}",
                                    m_i.to_string(),
                                    s_i.to_string()
                                ));
                                first = false
                            }
                            select_str.push_str(" }");
                        }
                    };

                    select_str
                }
                Type::Recur { ref t, ref s } => format!("μ{}.{}", t, s.to_string()),
                Type::TypeVar { ref t } => format!("{}", t),
                Type::End => String::from("end"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::global;
    use super::local;
    use super::Message;
    use super::PayloadType;
    use super::Role;

    #[test]
    fn new_role() {
        let alice = Role::new("Alice");
        assert!(String::from("Alice").eq(alice.name()));
        // Test alice.name() can be reused.
        assert!(String::from("Alice").eq(alice.name()));
    }

    #[test]
    fn new_message() {
        let msg = Message::new("l");
        assert!(String::from("l").eq(msg.label()));
        assert_eq!(msg.to_string(), String::from("l()"));

        let msg_with_payloads = Message::with_payload_type("l", "int");
        assert!(String::from("l").eq(msg_with_payloads.label()));
        assert_eq!(msg_with_payloads.to_string(), String::from("l(int)"));
    }

    #[test]
    fn example_global_type() {
        let sndr = Role::new("alice");
        let rcvr = Role::new("bob");
        let msg1 = Message::new("label1");
        let msg2 = Message::new("label2");

        let p1 = global::Type::interaction(&sndr, &rcvr);
        let p1_1 = global::Type::add_message(p1, msg1, global::Type::typevar("T"));
        let p1_2 = global::Type::add_message(p1_1, msg2, global::Type::end());
        let p = global::Type::recur("T", p1_2);

        match *p {
            global::Type::Recur { ref t, ref g } => {
                assert_eq!(t, "T");
                match **g {
                    global::Type::Interact { ref p, ref q, ref g } => {
                        assert!(Rc::ptr_eq(p, &sndr));
                        assert!(Rc::ptr_eq(q, &rcvr));
                        for (m_i, g_i) in g {
                            match m_i.label().as_str() {
                                "label1" => match **g_i {
                                    global::Type::TypeVar { ref t } => assert_eq!(t, "T"),
                                    _ => assert!(false),
                                },
                                "label2" => match **g_i {
                                    global::Type::End => assert!(true),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            }
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn example_local_type() {
        let sndr = Role::new("alice");
        let rcvr = Role::new("bob");
        let msg1 = Message::with_payload_type("label", "int");
        let msg2 = Message::with_payload_type("label2", "int");
        let msg3 = Message::with_payload_type("label3", "");

        let sel2 = local::Type::select(&sndr);
        let sel2_1 = local::Type::add_message(sel2, msg2, local::Type::typevar("T"));
        let sel2_2 = local::Type::add_message(sel2_1, msg3, local::Type::end());
        let br1 = local::Type::branch(&rcvr);
        let br1_1 = local::Type::add_message(br1, msg1, sel2_2); // Recv
        let p = local::Type::recur("T", br1_1);

        match *p {
            local::Type::Recur { ref t, ref s } => {
                assert_eq!(t, "T");
                match **s {
                    local::Type::Branch { ref p, ref s } => {
                        assert!(Rc::ptr_eq(p, &rcvr));
                        for (m_i, s_i) in s {
                            match m_i.label().as_str() {
                                "label" => {
                                    match **s_i {
                                        local::Type::Select { ref p, ref s } => {
                                            assert!(Rc::ptr_eq(p, &sndr));
                                            for (m_i, s_i) in s {
                                                match m_i.label().as_str() {
                                                    "label2" => match **s_i {
                                                        local::Type::TypeVar{ ref t } => assert_eq!(t.as_str(), "T"),
                                                        _ => assert!(false),
                                                    }
                                                    "label3" => match **s_i {
                                                        local::Type::End => assert!(true),
                                                        _ => assert!(false)
                                                    }
                                                    _ => assert!(false),
                                                }
                                            }
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn example_session_passing() {
        let sndr = Role::new("alice");
        let rcvr = Role::new("bob");

        let p = global::Type::interaction(&sndr, &rcvr);
        let l = Message::with_payload_session("label", local::Type::recur("T", local::Type::add_message(local::Type::branch(&Role::new("a")), Message::with_payload_type("L", "T"), local::Type::end())));
        let p2 = global::Type::add_message(p, l, global::Type::end());

        match *p2 {
            global::Type::Interact { ref p, ref q, ref g } => {
                assert_eq!(p.name(), sndr.name());
                assert_eq!(q.name(), rcvr.name());
                for (m_i, g_i) in g {
                    assert!(*m_i.label() == String::from("label"));
                    match m_i.payload {
                        PayloadType::Session(ref s) => {
                            match **s {
                                local::Type::Recur { ref t, ref s } => {
                                    assert!(*t == String::from("T"));
                                    match **s {
                                        local::Type::Branch { ref p, ref s } => {
                                            assert_eq!(*p.name(), String::from("a"));
                                            for (m_i, s_i) in s {
                                                assert!(*m_i.label() == String::from("L"));
                                                match m_i.payload {
                                                    PayloadType::BaseType(ref t) => assert!(*t == String::from("T")),
                                                    _ => assert!(false),
                                                }
                                                match **s_i {
                                                    local::Type::End => (),
                                                    _ => assert!(false),
                                                }
                                            }
                                        },
                                        _ => assert!(false),
                                    }
                                },
                                _ => assert!(false)
                            }
                        },
                        _ => assert!(false),
                    }
                    match **g_i {
                        global::Type::End => (),
                        _ => assert!(false),
                    }
                }
            },
            _ => assert!(false),
        }

        assert_eq!(p2.to_string(), "alice → bob:label(μT.a?L(T).end).end");
    }
}
