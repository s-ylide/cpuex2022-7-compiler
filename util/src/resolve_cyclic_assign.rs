use std::{collections::HashSet, hash::Hash};

#[derive(Debug, PartialEq)]
pub enum Assignment<T> {
    /// move `{1}` to `{0}`.
    Move(T, T),
    /// save `{0}`. same as Move(temp, `{0}`)
    Stash(T),
    /// restore `{0}`. same as Move(`{0}`, temp)
    Pop(T),
}

/// move `{1}` to `{0}`.
pub struct Mv<T>(pub T, pub T);

impl<T> Assignment<T> {
    #[inline]
    pub fn into_move(self, temp: T) -> Mv<T> {
        match self {
            Assignment::Move(x, y) => Mv(x, y),
            Assignment::Stash(x) => Mv(temp, x),
            Assignment::Pop(y) => Mv(y, temp),
        }
    }
}

/// resolves cyclic assignment using outer storage (one temporary register).
/// returns a sequence of assignment without identical move.
pub fn resolve_cyclic_assignment<T: Clone + Eq + Hash>(
    assigns: impl Iterator<Item = Mv<T>>,
) -> Vec<Assignment<T>> {
    let mut assigns: Vec<_> = assigns
        .filter_map(|Mv(x, y)| {
            if x != y {
                Some(Assignment::Move(x, y))
            } else {
                None
            }
        })
        .collect();
    let mut acycle = 0;
    loop {
        let heads: HashSet<_> = assigns[acycle..]
            .iter()
            .filter_map(|a| match a {
                Assignment::Move(_, h) | Assignment::Stash(h) => Some(h.clone()),
                Assignment::Pop(_) => None,
            })
            .collect();
        let cycle_begin = assigns[acycle..]
            .iter_mut()
            .partition_in_place(|assign| match assign {
                Assignment::Move(tail, _) | Assignment::Pop(tail) => !heads.contains(tail),
                Assignment::Stash(_) => true,
            });
        let len = assigns[acycle..].len();
        if len == 0 || len == cycle_begin + 1 {
            break assigns;
        }
        acycle += cycle_begin;
        if cycle_begin != 0 {
            continue;
        }
        let cycle_participant = match &assigns[acycle] {
            Assignment::Move(tail, _) | Assignment::Pop(tail) => tail.clone(),
            _ => unreachable!(),
        };
        assigns.insert(acycle, Assignment::Stash(cycle_participant.clone()));
        acycle += 1;
        assigns[acycle..].iter_mut().for_each(|a| {
            if let Assignment::Move(z, y) = a {
                if y == &cycle_participant {
                    *a = Assignment::Pop(z.clone())
                }
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_cyclic() {
        use Assignment::*;
        let v = resolve_cyclic_assignment([Mv(1, 1), Mv(2, 2)].into_iter());
        assert!(v.is_empty());
        let v = resolve_cyclic_assignment([Mv(2, 1), Mv(1, 2)].into_iter());
        assert_eq!(v, vec![Stash(2), Move(2, 1), Pop(1)]);
        let v = resolve_cyclic_assignment([Mv(2, 1), Mv(1, 2), Mv(4, 3), Mv(3, 4)].into_iter());
        assert_eq!(
            v,
            vec![Stash(2), Move(2, 1), Pop(1), Stash(4), Move(4, 3), Pop(3)]
        );
        let v = resolve_cyclic_assignment([Mv(2, 1), Mv(3, 2), Mv(4, 3)].into_iter());
        assert_eq!(v, vec![Move(4, 3), Move(3, 2), Move(2, 1)]);
        let v = resolve_cyclic_assignment([Mv(3, 2), Mv(2, 1), Mv(1, 3)].into_iter());
        assert_eq!(v, vec![Stash(3), Move(3, 2), Move(2, 1), Pop(1)]);
        let v = resolve_cyclic_assignment([Mv(1, 2), Mv(2, 3)].into_iter());
        assert_eq!(v, vec![Move(1, 2), Move(2, 3)]);
    }
}
