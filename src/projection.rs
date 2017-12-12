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

use std::rc::Rc;
use super::global::Type as G;
use super::local::Type as S;
use super::Role;

/// Converts a global::Type into a local::Type.
///
/// This implements the projection G↾q defined in Definition A.1.
///
pub fn project(global_type: &Box<G>, role: &Rc<Role>) -> Option<Box<S>> {
    match **global_type {
        G::Interact {
            ref p,
            ref q,
            ref g,
        } => {
            if Rc::ptr_eq(&role, &p) {
                let mut sel = S::select(q);
                for (m_i, g_i) in g {
                    let projected_s = project(&g_i, role);
                    match projected_s {
                        Some(projected_s) => {
                            sel = S::add_message(sel, m_i.clone(), projected_s);
                            ()
                        }
                        None => (),
                    }
                }
                Some(sel)
            } else if Rc::ptr_eq(&role, &q) {
                let mut br = S::branch(p);
                for (m_i, g_i) in g {
                    let projected_s = project(&g_i, role);
                    match projected_s {
                        Some(projected_s) => {
                            br = S::add_message(br, m_i.clone(), projected_s);
                            ()
                        }
                        None => (),
                    }
                }
                Some(br)
            } else {
                // p != role != q
                match g.len() {
                    1 => {
                        let item = g.iter().next();
                        match item {
                            Some(ref item) => project(item.1, role),
                            None => None,
                        }
                    }
                    _ => {
                        let mut iter = g.iter();
                        let first_item = iter.next();
                        match first_item {
                            Some(ref first_item) => {
                                let mut merged = project(first_item.1, role);
                                for (_, g_i) in iter {
                                    let projected_s = project(&g_i, role);
                                    match projected_s {
                                        Some(ref projected_s) => {
                                            match merged {
                                                Some(merged_) => {
                                                    merged = merge(&merged_, projected_s);
                                                    ()
                                                }
                                                None => (),
                                            }
                                            ()
                                        }
                                        None => (),
                                    }
                                }
                                merged
                            }
                            None => None,
                        }
                    }
                }
            }
        }
        G::Recur { ref t, ref g } => {
            let projected_s = project(g, role);
            match projected_s {
                Some(ref projected_s) => Some(S::recur(t, projected_s.clone())),
                None => None,
            }
        }
        G::TypeVar { ref t } => Some(S::typevar(t)),
        G::End => Some(S::end()),
    }
}

/// Merges two local session types.
///
/// This implements the merge operator Π on session types defined in Definition A.1.
///
fn merge(l: &Box<S>, r: &Box<S>) -> Option<Box<S>> {
    let (ref box_l, ref box_r) = (&*l, &*r);
    match (box_l.as_ref(), box_r.as_ref()) {
        (&S::Branch { ref p, ref s },
         &S::Branch {
             p: ref p_r,
             s: ref s_r,
         }) => {
            if Rc::ptr_eq(p, p_r) {
                let mut br = S::branch(p);
                for (m_i, s_i) in s {
                    if s_r.contains_key(m_i) {
                        // Intersect case
                        let s_j = s_r.get(m_i);
                        match s_j {
                            Some(s_j) => {
                                let merged_br = merge(s_i, s_j);
                                match merged_br {
                                    Some(merged_br) => {
                                        br = S::add_message(br, m_i.clone(), merged_br);
                                        ()
                                    }
                                    None => (),
                                }
                            }
                            None => (),
                        }
                    } else {
                        // Only in s case
                        br = S::add_message(br, m_i.clone(), s_i.clone())
                    }
                }
                for (m_j, s_j) in s_r {
                    if !s.contains_key(m_j) {
                        // Only in s_r case
                        br = S::add_message(br, m_j.clone(), s_j.clone())
                    }
                }
                Some(br)
            } else {
                None
            }
        }
        (&S::Select { ref p, ref s },
         &S::Select {
             p: ref p_r,
             s: ref s_r,
         }) => {
            if Rc::ptr_eq(p, p_r) {
                let mut sel = S::select(p);
                for (m_i, s_i) in s {
                    if s_r.contains_key(m_i) {
                        // Note: s_i must be equal to s_r.entry(m_i)
                        sel = S::add_message(sel, m_i.clone(), s_i.clone())
                    }
                }
                Some(sel)
            } else {
                None
            }
        }
        (&S::Recur { ref t, ref s },
         &S::Recur {
             t: ref t_r,
             s: ref s_r,
         }) => {
            if t == t_r {
                let s_merged = merge(s, s_r);
                match s_merged {
                    Some(s_) => Some(S::recur(t, s_)),
                    None => None,
                }
            } else {
                None
            }
        }
        (&S::TypeVar { ref t }, &S::TypeVar { t: ref t_r }) => {
            if t == t_r { Some(S::typevar(t)) } else { None }
        }
        (&S::End, &S::End) => Some(S::end()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use global;
    use local;
    use Message;
    use Role;

    #[test]
    fn test_projection() {
        let sndr = Role::new("alice");
        let rcvr = Role::new("bob");
        let msg1 = Message::new("label1");
        let msg2 = Message::new("label2");

        let p1 = global::Type::interaction(&sndr, &rcvr);
        let p1_1 = global::Type::add_message(p1, msg1, global::Type::typevar("T"));
        let p1_2 = global::Type::add_message(p1_1, msg2, global::Type::end());
        let p0 = global::Type::recur("T", p1_2);

        let local_alice = super::project(&p0, &sndr);
        let local_bob = super::project(&p0, &rcvr);

        match local_alice {
            Some(ref t) => {
                match **t {
                    local::Type::Recur { ref t, ref s } => {
                        assert_eq!(t, "T");
                        match **s {
                            local::Type::Select { ref p, ref s } => {
                                assert!(Rc::ptr_eq(p, &rcvr));
                                for (m_i, s_i) in s {
                                    match m_i.label().as_str() {
                                        "label1" => {
                                            match **s_i {
                                                local::Type::TypeVar { ref t } => {
                                                    assert_eq!(t, "T")
                                                }
                                                _ => assert!(false),
                                            }
                                        }
                                        "label2" => {
                                            match **s_i {
                                                local::Type::End => assert!(true),
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
            None => assert!(false),
        };

        match local_bob {
            Some(ref t) => {
                match **t {
                    local::Type::Recur { ref t, ref s } => {
                        assert_eq!(t, "T");
                        match **s {
                            local::Type::Branch { ref p, ref s } => {
                                assert!(Rc::ptr_eq(p, &sndr));
                                for (m_i, s_i) in s {
                                    match m_i.label().as_str() {
                                        "label1" => {
                                            match **s_i {
                                                local::Type::TypeVar { ref t } => {
                                                    assert_eq!(t, "T")
                                                }
                                                _ => assert!(false),
                                            }
                                        }
                                        "label2" => {
                                            match **s_i {
                                                local::Type::End => assert!(true),
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
            None => assert!(false),
        }
    }
}
