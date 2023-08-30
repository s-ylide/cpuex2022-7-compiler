use std::{cell::RefCell, collections::HashMap, hash::Hash, rc::Rc};

pub struct UnionFind<Key, GroupId> {
    index: HashMap<Key, UFNode<Key, GroupId>>,
}

enum UFNode<Key, GroupId> {
    Root(Rc<RefCell<UFRoot<GroupId>>>),
    Node(Rc<RefCell<Key>>),
}

impl<Key, GroupId> UFNode<Key, GroupId> {
    fn as_root(&self) -> Option<&Rc<RefCell<UFRoot<GroupId>>>> {
        if let Self::Root(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Clone)]
struct UFRoot<GroupId> {
    group_id: GroupId,
    rank: usize,
}

impl<GroupId> UFRoot<GroupId> {
    fn new(group_id: GroupId) -> Self {
        Self { group_id, rank: 0 }
    }
}

impl<Key, GroupId> UnionFind<Key, GroupId> {
    pub fn new() -> Self {
        Self {
            index: Default::default(),
        }
    }

    pub fn clear(&mut self) {
        self.index.clear()
    }
}

impl<Key, GroupId> Default for UnionFind<Key, GroupId> {
    fn default() -> Self {
        Self::new()
    }
}

pub enum UnionResult<GroupId> {
    Merged { new: GroupId, old: GroupId },
    Unchanged { common: GroupId },
}

impl<Key: Eq + Hash + Clone, GroupId: Eq + Clone> UnionFind<Key, GroupId> {
    /// create a new set from given key.
    pub fn make_set(&mut self, key: Key, group_id: GroupId) {
        let v = UFNode::Root(Rc::new(RefCell::new(UFRoot::new(group_id))));
        self.index.insert(key, v);
    }
    pub fn is_equiv(&self, key1: &Key, key2: &Key) -> Option<bool> {
        let kx = self.get_root(key1)?;
        let ky = self.get_root(key2)?;
        Some(kx == ky)
    }
    #[must_use]
    pub fn union(&mut self, key1: &Key, key2: &Key) -> Option<UnionResult<GroupId>> {
        let kx = self.get_root(key1)?;
        let ky = self.get_root(key2)?;
        use std::cmp::Ordering::*;
        let nodex_freeze = self
            .index
            .get(&kx)
            .unwrap()
            .as_root()
            .unwrap()
            .borrow()
            .clone();
        let nodey_freeze = self
            .index
            .get(&ky)
            .unwrap()
            .as_root()
            .unwrap()
            .borrow()
            .clone();
        use UnionResult::*;
        let o = nodex_freeze.rank.cmp(&nodey_freeze.rank);
        Some(match o {
            Less => {
                *self.index.get_mut(&kx).unwrap() = UFNode::Node(Rc::new(RefCell::new(ky)));
                Merged {
                    new: nodey_freeze.group_id,
                    old: nodex_freeze.group_id,
                }
            }
            Greater => {
                *self.index.get_mut(&ky).unwrap() = UFNode::Node(Rc::new(RefCell::new(kx)));
                Merged {
                    new: nodex_freeze.group_id,
                    old: nodey_freeze.group_id,
                }
            }
            Equal => {
                if kx != ky {
                    let nodex = &mut *self.index.get(&kx).unwrap().as_root().unwrap().borrow_mut();
                    let nodey = &mut *self.index.get(&ky).unwrap().as_root().unwrap().borrow_mut();
                    nodey.group_id = nodex.group_id.clone();
                    nodex.rank += 1;
                    Merged {
                        new: nodex_freeze.group_id,
                        old: nodey_freeze.group_id,
                    }
                } else {
                    Unchanged {
                        common: nodex_freeze.group_id,
                    }
                }
            }
        })
    }
    /// get group_id of given key, with path-compressing.
    pub fn get_root_id(&self, key: &Key) -> Option<GroupId> {
        self.get_root(key).map(|k| {
            self.index
                .get(&k)
                .unwrap()
                .as_root()
                .unwrap()
                .borrow()
                .group_id
                .clone()
        })
    }
    /// get root key of given key, with path-compressing.
    fn get_root(&self, key: &Key) -> Option<Key> {
        let mut node = self.index.get(key)?;
        let mut stack: Vec<Rc<RefCell<Key>>> = Vec::new();
        loop {
            match node {
                UFNode::Root(_) => {
                    let key = match stack.pop() {
                        Some(key) => {
                            let key = key.borrow().clone();
                            for child_key in &stack {
                                *child_key.borrow_mut() = key.clone();
                            }
                            key
                        }
                        None => key.clone(),
                    };
                    break Some(key);
                }
                UFNode::Node(parent) => {
                    let parent = parent.clone();
                    node = self.index.get(&parent.borrow().clone()).unwrap();
                    stack.push(parent);
                }
            }
        }
    }
}
