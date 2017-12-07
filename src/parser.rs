use nom::{IResult, is_alphanumeric};
use std::rc::Rc;
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

// Public parse functions.

/// Returns parsed `global::Type` from a given `String`.
///
pub fn parse_global_type(s: String) -> Option<Box<global::Type>> {
    let g = global(s.as_bytes());
    match g {
        IResult::Done(unparsed, global_type) => {
            if unparsed.len() > 0 {
                println!("Unparsed bytes: {:?}", unparsed);
            }
            Some(global_type)
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
pub fn parse_local_type(s: String) -> Option<Box<local::Type>> {
    let l = local(s.as_bytes());
    match l {
        IResult::Done(unparsed, local_type) => {
            if unparsed.len() > 0 {
                println!("Unparsed bytes: {:?}", unparsed);
            }
            Some(local_type)
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
//

// ident   = [A-Za-z][A-Za-z0-9]* // TODO: current definition is [A-Za-z0-9]*
named!(ident<String>,
       map!(take_while!(is_alphanumeric),slice_to_string));

// role    = ident
named!(role<Rc<Role>>,
       map!(call!(ident), |s: String| Role::new(&*s)));

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
named!(global<Box<global::Type>>,
       alt!(
           call!(interaction) |
           call!(end)         |
           call!(recur)       |
           call!(typevar)
       )
);

// interact = sendrecv | '{' sendrecv (',' sendrecv)+ '}'
named!(interaction<Box<global::Type>>,
       ws!(do_parse!(
               sndr: call!(role) >>
               alt!( tag!("->") | tag!("→") ) >>
               rcvr: call!(role) >>
               tag!(":") >>
               g: alt!(
                    call!(sendrecv)  => {|t: _| singleton_vec(t)} |
                    call!(sendrecvs) => {|v: _| v}) >>
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
named!(sendrecv<(Message, Box<global::Type>)>,
       ws!(do_parse!(
               m: call!(message) >>
               tag!(".") >>
               g: call!(global) >>
               ((m, g))
       ))
);

named!(sendrecvs<Vec<(Message, Box<global::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(sendrecv)) >>
               tag!("}") >>
               (l)
       ))
);

// recur    = '*' ident '.' global
named!(recur<Box<global::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               tag!(".") >>
               g: call!(global) >>
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
named!(local<Box<local::Type>>,
       alt!(
           call!(branch)   |
           call!(select)   |
           call!(lend)     |
           call!(lrecur)   |
           call!(ltypevar)
       )
);

// branch   = recv | '{' recv (',' recv)+ '}'
named!(branch<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role) >>
               tag!("&") >>
               s: alt!(
                   call!(recv)  => {|t: _| singleton_vec(t)} |
                   call!(recvs) => {|v: _| v}) >>
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
named!(recv<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("?") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local) >>
               ((m, s))
       ))
);

named!(recvs<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(recv)) >>
               tag!("}") >>
               (l)
       ))
);

// select   = send | '{' send (',' send)+ '}'
named!(select<Box<local::Type>>,
       ws!(do_parse!(
               p: call!(role) >>
               alt!( tag!("+") | tag!("⊕") ) >>
               s: alt!(
                   call!(send)  => {|t: _| singleton_vec(t)} |
                   call!(sends) => {|v: _| v}) >>
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
named!(send<(Message, Box<local::Type>)>,
       ws!(do_parse!(
               tag!("!") >>
               m: call!(message) >>
               tag!(".") >>
               s: call!(local) >>
               ((m, s))
       ))
);

named!(sends<Vec<(Message, Box<local::Type>)>>,
       ws!(do_parse!(
               tag!("{") >>
               l: separated_list!(tag!(","), call!(send)) >>
               tag!("}") >>
               (l)
       ))
);

// lrecur   = '*' ident '.' local
named!(lrecur<Box<local::Type>>,
       ws!(do_parse!(
               alt!( tag!("μ") | tag!("*") ) >>
               t: call!(ident) >>
               tag!(".") >>
               s: call!(local) >>
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
