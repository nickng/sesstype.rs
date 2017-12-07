use nom::{IResult, is_alphanumeric};
use std::rc::Rc;
use std::collections::HashMap;
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

// Public parse functions.

/// Returns parsed `global::Type` from a given `String`.
///
pub fn parse_global_type(s: String) -> Option<(Box<global::Type>, RoleRegistry)> {
    let mut registry = RoleRegistry::new();
    let g = global(s.as_bytes(), &mut registry);
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
    let l = local(s.as_bytes(), &mut registry);
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

// ident   = [A-Za-z][A-Za-z0-9]* // TODO: current definition is [A-Za-z0-9]*
named!(ident<String>,
       map!(take_while!(is_alphanumeric),slice_to_string));

// role    = ident
named_args!(role<'a>(r: &'a mut RoleRegistry)<Rc<Role>>,
       map!(call!(ident), |s: String| r.get_or_create_role(s)));

// message = ident payload
named!(message<Message>,
       do_parse!(
           label: call!(ident) >>
           pt: call!(payload) >>
           (match pt {
               PayloadType::BaseType(s) => Message::with_payload_type(&*label, &*s),
               PayloadType::Session(_)  => Message::new(&*label),
               PayloadType::Empty       => Message::new(&*label),
           })
       )
);

// payload = '()' | '(' ident ')'
named!(payload<PayloadType>,
       do_parse!(
           tag!("(") >>
           t: call!(ident) >>
           tag!(")") >>
           (if t == "" {
               PayloadType::Empty
           } else {
               PayloadType::BaseType(t)}
           )
       )
);

// global   = role '->' role ':' interact
//          | recur
//          | typevar
//          | end
named_args!(global<'a>(r: &'a mut RoleRegistry)<Box<global::Type>>,
       alt!(
           call!(interaction, r) |
           call!(end)            |
           call!(recur, r)       |
           call!(typevar)
       )
);

// interact = sendrecv | '{' sendrecv (',' sendrecv)+ '}'
named_args!(interaction<'a>(r: &'a mut RoleRegistry)<Box<global::Type>>,
       ws!(do_parse!(
               sndr: call!(role, r) >>
               alt!( tag!("->") | tag!("→") ) >>
               rcvr: call!(role, r) >>
               tag!(":") >>
               g: alt!(
                    call!(sendrecv, r)  => {|t: _| singleton_vec(t)} |
                    call!(sendrecvs, r) => {|v: _| v}) >>
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
named_args!(sendrecv<'a>(r: &'a mut RoleRegistry)<(Message, Box<global::Type>)>,
       ws!(do_parse!(
               m: call!(message) >>
               tag!(".") >>
               g: call!(global, r) >>
               ((m, g))
       ))
);

named_args!(sendrecvs<'a>(r: &'a mut RoleRegistry)<Vec<(Message, Box<global::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(sendrecv, r)) >>
               tag!("}") >>
               (l)
       ))
);

// recur    = '*' ident '.' global
named_args!(recur<'a>(r: &'a mut RoleRegistry)<Box<global::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               tag!(".") >>
               g: call!(global, r) >>
               (global::Type::recur(&*t, g))
       ))
);

// typevar  = ident
named!(typevar<Box<global::Type>>,
    map!(call!(ident), |t: String| global::Type::typevar(&*t))
);

// end      = 'end'
named!(end<Box<global::Type>>,
       map!(tag!("end"), |_| global::Type::end())
);

// local    = role '&' branch
//          | role '+' select
//          | lrecur
//          | ltypevar
//          | end
named_args!(local<'a>(r: &'a mut RoleRegistry)<Box<local::Type>>,
       alt!(
           call!(branch, r) |
           call!(select, r) |
           call!(lend)      |
           call!(lrecur, r) |
           call!(ltypevar)
       )
);

// branch   = recv | '{' recv (',' recv)+ '}'
named_args!(branch<'a>(r: &'a mut RoleRegistry)<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role, r) >>
               tag!("&") >>
               s: alt!(
                   call!(recv, r)  => {|t: _| singleton_vec(t)} |
                   call!(recvs, r) => {|v: _| v}) >>
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
named_args!(recv<'a>(r: &'a mut RoleRegistry)<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("?") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local, r) >>
               ((m, s))
       ))
);

named_args!(recvs<'a>(r: &'a mut RoleRegistry)<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(recv, r)) >>
               tag!("}") >>
               (l)
       ))
);

// select   = send | '{' send (',' send)+ '}'
named_args!(select<'a>(r: &'a mut RoleRegistry)<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role, r) >>
               alt!( tag!("+") | tag!("⊕") ) >>
               s: alt!(
                   call!(send, r)  => {|t: _| singleton_vec(t)} |
                   call!(sends, r) => {|v: _| v}) >>
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
named_args!(send<'a>(r: &'a mut RoleRegistry)<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("!") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local, r) >>
               ((m, s))
       ))
);

named_args!(sends<'a>(r: &'a mut RoleRegistry)<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(send, r)) >>
               tag!("}") >>
               (l)
       ))
);

// lrecur   = '*' ident '.' local
named_args!(lrecur<'a>(r: &'a mut RoleRegistry)<Box<local::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               tag!(".") >>
               s: call!(local, r) >>
               (local::Type::recur(&*t, s))
       ))
);

// ltypevar = ident
named!(ltypevar<Box<local::Type>>,
    map!(call!(ident), |t: String| local::Type::typevar(&*t))
);

// lend     = "end"
named!(lend<Box<local::Type>>,
       map!(tag!("end"), |_| local::Type::end())
);

#[cfg(test)]
mod tests {
    use super::{parse_global_type, parse_local_type};
    use super::super::project;

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
        assert_eq!(l.unwrap().to_string(), "μT.A!l(int).A?l2().T");
    }
}
