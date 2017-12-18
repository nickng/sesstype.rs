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

use nom::{IResult, is_alphanumeric, is_alphabetic};
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use super::{global, local, Message, PayloadType, Role};

// Helper functions

/// Converts a slice into a `String`.
///
/// Helper function that converts a slice of `u8` into `String`
///
fn slice_to_string(s: &[u8]) -> String {
    String::from_utf8(Vec::from(s)).unwrap()
}

/// Converts a value to a singleton `Vec`.
///
/// Helper function to do in a single step.
///
fn singleton_vec<T>(t: T) -> Vec<T> {
    let mut v = Vec::new();
    v.push(t);
    v
}

/// Registry of roles in a parsed protocol.
///
/// Only the parser can create a role registry, and is returned by the
/// parsing functions. Users can use the registry to find roles parsed
/// from a {global,local}::Type, where each role name maps to a single
/// instance of `Role`.
///
pub struct RoleRegistry {
    roles: HashMap<String, Rc<Role>>,
}

impl RoleRegistry {
    /// Creates a new empty role registry
    ///
    fn new() -> RoleRegistry {
        RoleRegistry { roles: HashMap::new() }
    }

    /// Finds existing role with the same name and return its pointer,
    /// or create new `Role` if role with the name does not exist.
    ///
    fn get_or_create_role(&mut self, name: String) -> Rc<Role> {
        if self.roles.contains_key(&name) {
            (*self.roles.get(&*name).unwrap()).clone()
        } else {
            let role = Role::new(&name);
            self.roles.insert(name, role.clone());
            role
        }
    }

    /// Returns a role instance given its name.
    ///
    pub fn find_role_str(&self, name: &str) -> Option<Rc<Role>> {
        self.find_role(String::from(name))
    }

    /// Returns a role instance given its name.
    ///
    pub fn find_role(&self, name: String) -> Option<Rc<Role>> {
        match self.roles.get(&name) {
            Some(r) => Some(r.clone()),
            None => None,
        }
    }
}

/// Valid TypeVars defined in the protocol.
///
/// A type variable T can only appear in the body of a recur{ t: "T", body }.
///
struct TypeVars {
    typevars: HashSet<String>,
}

impl TypeVars {
    /// Creats a new empty TypeVar registry.
    ///
    fn new() -> TypeVars {
        TypeVars { typevars: HashSet::new() }
    }

    /// Adds a typevar to the scope.
    ///
    /// An ident that matches a typevar is parsed as a valid typevar.
    ///
    fn add(&mut self, typevar: String) -> String {
        self.typevars.insert(typevar.clone());
        typevar
    }

    /// Checks if a potential typevar is in scope.
    ///
    /// If the typevar is in scope, the typevar would be converted to
    /// a Type::TypeVar, otherwise it may be considered a Role or other
    /// possible ambiguous ident.
    ///
    fn is_valid(&self, typevar: &String) -> bool {
        self.typevars.contains(typevar)
    }
}

// Public parse functions.

/// Returns parsed `global::Type` from a given `String`.
///
pub fn parse_global_type(s: String) -> Option<(Box<global::Type>, RoleRegistry)> {
    let mut registry = RoleRegistry::new();
    let mut typevars = TypeVars::new();
    let g = global(s.as_bytes(), &mut registry, &mut typevars);
    match g {
        IResult::Done(unparsed, global_type) => {
            if unparsed.len() > 0 {
                println!("Unparsed bytes: {:?}", unparsed);
            }
            Some((global_type, registry))
        }
        IResult::Error(e) => {
            println!("Parse error: {:?}", e);
            None
        }
        IResult::Incomplete(n) => {
            println!("Parse incomplete: {:?}", n);
            None
        }
    }
}

/// Returns parsed `local::Type` from a given `String`.
///
pub fn parse_local_type(s: String) -> Option<(Box<local::Type>, RoleRegistry)> {
    let mut registry = RoleRegistry::new();
    let mut typevars = TypeVars::new();
    let l = local(s.as_bytes(), &mut registry, &mut typevars);
    match l {
        IResult::Done(unparsed, local_type) => {
            if unparsed.len() > 0 {
                println!("Unparsed bytes: {:?}", unparsed);
            }
            Some((local_type, registry))
        }
        IResult::Error(e) => {
            println!("Parse error: {:?}", e);
            None
        }
        IResult::Incomplete(n) => {
            println!("Parse incomplete: {:?}", n);
            None
        }
    }
}


// For reference, the grammar of each non-terminal symbol are shown inline.
//

// ident   = [A-Za-z][A-Za-z0-9]*
named!(ident<String>,
       do_parse!(
           prefix: take_while!(is_alphabetic) >>
           suffix: take_while!(is_alphanumeric) >>
          (slice_to_string(prefix) + &slice_to_string(suffix))
       )
);

// role    = ident
named_args!(role<'a>(r: &'a mut RoleRegistry)<Rc<Role>>,
       map!(call!(ident), |s: String| r.get_or_create_role(s)));

// message = ident payload
named!(message<Message>,
       do_parse!(
           label: call!(ident) >>
           payload: call!(payload) >>
           (Message {
               label: String::from(label),
               payload: payload,
           })
       )
);

// payload = '()' | '(' ident ')' | '(' local ')'
named!(payload<PayloadType>,
       delimited!(
           tag!("("),
           alt_complete!(
               call!(local, &mut RoleRegistry::new(), &mut TypeVars::new()) => {|s| PayloadType::Session(s)} |
               call!(ident)                                                 => {|t| if t == "" {PayloadType::Empty} else {PayloadType::BaseType(t)}}
           ),
           tag!(")")
       )
);

// global   = role '->' role ':' interact
//          | recur
//          | typevar
//          | end
named_args!(global<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<global::Type>>,
       ws!(alt_complete!(
           call!(interaction, r, tv) |
           call!(end)                | // Check end before typevar
           call!(recur, r, tv)       |
           call!(typevar, tv)
       ))
);

// interact = sendrecv | '{' sendrecv (',' sendrecv)+ '}'
named_args!(interaction<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<global::Type>>,
       ws!(do_parse!(
               sndr: call!(role, r) >>
               alt!( tag!("->") | tag!("→") ) >>
               rcvr: call!(role, r) >>
               tag!(":") >>
               g: alt!(
                    call!(sendrecv, r, tv)  => {|t: _| singleton_vec(t)} |
                    call!(sendrecvs, r, tv) => {|v: _| v}) >>
               ({
                   let mut stmt = global::Type::interaction(&sndr, &rcvr);
                   for mg_i in g.into_iter() {
                       stmt = global::Type::add_message(stmt, mg_i.0, mg_i.1);
                   }
                   stmt
               })
       ))
);

// sendrecv = message '.' global
named_args!(sendrecv<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<(Message, Box<global::Type>)>,
       ws!(do_parse!(
               m: call!(message) >>
               tag!(".") >>
               g: call!(global, r, tv) >>
               ((m, g))
       ))
);

named_args!(sendrecvs<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Vec<(Message, Box<global::Type>)>>,
       ws!(delimited!(
               tag!("{"),
               separated_list!(tag!(","), call!(sendrecv, r, tv)),
               tag!("}")
       ))
);

// recur    = '*' ident '.' global
named_args!(recur<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<global::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               v: expr_res!({ let res: Result<String, u8> = Ok(tv.add(t)); res }) >>
               tag!(".") >>
               g: call!(global, r, tv) >>
               (global::Type::recur(&v, g))
       ))
);

// typevar  = ident
named_args!(typevar<'a>(tv: &'a mut TypeVars)<Box<global::Type>>,
    do_parse!(
        s: call!(ident) >>
        e: expr_opt!({ if tv.is_valid(&s) { Some(global::Type::typevar(&s)) } else { None } }) >>
        (e)
    )
);

// end      = 'end'
named!(end<Box<global::Type>>,
       map!(tag!("end"), |_| global::Type::end())
);

// local    = role branch
//          | role select
//          | lrecur
//          | ltypevar
//          | end
named_args!(local<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<local::Type>>,
       ws!(alt_complete!(
           call!(branch, r, tv) |
           call!(select, r, tv) |
           call!(lend)          |
           call!(lrecur, r, tv) |
           call!(ltypevar, tv)
       ))
);

// branch   = recv | '&{' recv (',' recv)+ '}'
named_args!(branch<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role, r) >>
               s: alt!(
                   call!(recv, r, tv)  => {|t: _| singleton_vec(t)} |
                   call!(recvs, r, tv) => {|v: _| v}) >>
               ({
                   let mut stmt = local::Type::branch(&p);
                   for ms_i in s.into_iter() {
                       stmt = local::Type::add_message(stmt, ms_i.0, ms_i.1);
                   }
                   stmt
               })
       ))
);

// recv     = '?' message '.' local
named_args!(recv<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("?") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local, r, tv) >>
               ((m, s))
       ))
);

named_args!(recvs<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               tag!("&") >>
               recvs: delimited!(
                   tag!("{"),
                   separated_list!(tag!(","), call!(recv, r, tv)),
                   tag!("}")
               ) >>
               (recvs)
       ))
);

// select   = send | '+{' send (',' send)+ '}'
named_args!(select<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role, r) >>
               s: alt!(
                   call!(send, r, tv)  => {|t: _| singleton_vec(t)} |
                   call!(sends, r, tv) => {|v: _| v}) >>
               ({
                   let mut stmt = local::Type::select(&p);
                   for ms_i in s.into_iter() {
                       stmt = local::Type::add_message(stmt, ms_i.0, ms_i.1);
                   }
                   stmt
               })
       ))
);

// send     = '!' message '.' local
named_args!(send<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("!") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local, r, tv) >>
               ((m, s))
       ))
);

named_args!(sends<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               alt!( tag!("+") | tag!("⊕") ) >>
               sends: delimited!(
                   tag!("{"),
                   separated_list!(tag!(","), call!(send, r, tv)),
                   tag!("}")
               ) >>
               (sends)
           ))
);

// lrecur   = '*' ident '.' local
named_args!(lrecur<'a>(r: &'a mut RoleRegistry, tv: &'a mut TypeVars)<Box<local::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               v: expr_res!({ let res: Result<String, u8> = Ok(tv.add(t)); res }) >>
               tag!(".") >>
               s: call!(local, r, tv) >>
               (local::Type::recur(&v, s))
       ))
);

// ltypevar = ident
named_args!(ltypevar<'a>(tv: &'a mut TypeVars)<Box<local::Type>>,
    do_parse!(
        s: call!(ident) >>
        e: expr_opt!({ if tv.is_valid(&s) { Some(local::Type::typevar(&s)) } else { None } }) >>
        (e)
    )
);

// lend     = "end"
named!(lend<Box<local::Type>>,
       map!(tag!("end"), |_| local::Type::end())
);

#[cfg(test)]
mod tests {
    use super::{parse_global_type, parse_local_type};
    use super::super::{global, project};

    #[test]
    fn test_parse_global() {
        let g = parse_global_type(String::from("* T .A->B:{ l(int).T}"));
        assert_eq!(g.unwrap().0.to_string(), "μT.A → B:l(int).T");
    }

    #[test]
    fn test_parse_local() {
        let l = parse_local_type(String::from("*T .A&{?l(int).T}"));
        assert_eq!(l.unwrap().0.to_string(), "μT.A?l(int).T");
    }

    #[test]
    fn test_parse_project() {
        let g = parse_global_type(String::from("* T .A->B:{ l(int).B->A:{ l2().T } }"));
        let (global_type, registry) = g.unwrap();
        let l = project(&global_type, &registry.find_role_str("A").unwrap());
        assert_eq!(l.unwrap().to_string(), "μT.B!l(int).B?l2().T");
    }

    #[test]
    fn test_parse_ambiguous() {
        let g = parse_global_type(String::from("*T.A"));
        match g {
            Some(_) => assert!(false), // Not expecting this to parse
            None => (),
        }
    }

    #[test]
    fn test_parse_ambiguous2() {
        let g = parse_global_type(String::from("*T.end"));
        match g {
            Some(parsed) => {
                let (t, _reg) = parsed;
                match *t {
                    global::Type::Recur { ref t, ref g } => {
                        assert_eq!(*t, String::from("T"));
                        match **g {
                            global::Type::End => (),
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            None => assert!(false),
        }
    }

    #[test]
    fn test_parse_ambiguous3() {
        let g = parse_global_type(String::from("*T.T"));
        match g {
            Some(parsed) => {
                let (t, _reg) = parsed;
                match *t {
                    global::Type::Recur { ref t, ref g } => {
                        assert_eq!(*t, String::from("T"));
                        match **g {
                            global::Type::TypeVar { ref t } => assert_eq!(*t, String::from("T")),
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            None => assert!(false),
        }
    }

    #[test]
    fn test_parse_ambiguous4() {
        let g = parse_global_type(String::from("*T.A->B: { l().end }"));
        match g {
            Some(parsed) => {
                let (t, reg) = parsed;
                match *t {
                    global::Type::Recur { ref t, ref g } => {
                        assert_eq!(*t, String::from("T"));
                        match **g {
                            global::Type::Interact {
                                ref p,
                                ref q,
                                ref g,
                            } => {
                                assert_eq!(reg.find_role_str("A").unwrap().name(), p.name());
                                assert_eq!(reg.find_role_str("B").unwrap().name(), q.name());
                                for (m, g) in g {
                                    assert_eq!(*m.label(), String::from("l"));
                                    match **g {
                                        global::Type::End => (),
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
            None => assert!(false),
        }
    }
}
