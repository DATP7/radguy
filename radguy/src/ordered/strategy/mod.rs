use std::{
    cmp::{Ordering, Reverse},
    fmt::Display,
    hash::Hash,
    ops::Add,
};

mod binary_heap;
mod hashmap;
mod lazy;
mod orx;

pub use binary_heap::BinaryHeapStrategy;
pub use hashmap::HashMapStrategy;
pub use lazy::LazyHeap;
pub use orx::OrxStrategy;

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum StrategyWeight {
    Infinity,
    Num(u64),
}

impl Ord for StrategyWeight {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Infinity, Self::Infinity) => Ordering::Equal,
            (Self::Infinity, _) => Ordering::Greater,
            (_, Self::Infinity) => Ordering::Less,
            (Self::Num(x), Self::Num(y)) => x.cmp(y),
        }
    }
}

impl PartialOrd for StrategyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for StrategyWeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Infinity => write!(f, "∞"),
            Self::Num(x) => write!(f, "{x}"),
        }
    }
}

impl Add for StrategyWeight {
    type Output = Self;

    #[track_caller]
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Num(r), Self::Num(l)) => Self::Num(l + r),
            _ => Self::Infinity,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StrategyItem<T>(pub StrategyWeight, pub T);

impl<T> StrategyItem<T> {
    pub const fn infinite(value: T) -> Self {
        Self(StrategyWeight::Infinity, value)
    }

    pub const fn reversed(self) -> Reverse<Self> {
        Reverse(self)
    }
}

impl<T> Ord for StrategyItem<T> {
    fn cmp(&self, Self(o, _): &Self) -> std::cmp::Ordering {
        let Self(s, _) = self;
        s.cmp(o)
    }
}
impl<T> PartialOrd for StrategyItem<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialEq for StrategyItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for StrategyItem<T> {}

pub trait Strategy<T> {
    /// Extract the element in the strategy with the lowest weight
    ///
    /// Returns `None` if there are no more elements in the strategy
    // TODO: should we just have an iterator instead?
    fn extract_min(&mut self) -> Option<T>;
}

// We have `LeftSliced` and `RightSliced` so we can easily have the same implementation of
// `SliceLeft` and `SliceRight` but with different input/output types.
// For example, consider `OrxStrategy<(T, U), PH>`, where `PH: PriorityQueue<(T, U)>`.
// We want to be able to treat `PH` as just a `PriorityQueue<(T, U)>`, but if we just have
// ```rust
// impl<T,
//      U,
//      TH: PriorityQueue<T>,
//      PH: PriorityQueue<(T, U)>
// > SliceRight<T, U> for OrxStrategy<(T, U), PH> {
//  type Output = TH;
//  fn slice_right(self, right: U) -> Self::Output;
// }
// ```
//
// Here, `TH` and `PH` are not related by any constraints, so slicing a binary heap could yield a
// quatenary heap. This isn't a problem in theory, but it means that we need to specify our desired
// output type whenever we slice a heap, which isn't ideal. Furthermore, in practice, we usually
// just want to use the same underlying heap type everywhere, so fixing the output for each heap
// isn't a problem.
pub trait LeftSliced<T, U>: Strategy<(T, U)> {
    type SlicedLeft: Strategy<U>;
}

pub trait RightSliced<T, U>: Strategy<(T, U)> {
    type SlicedRight: Strategy<T>;
}

pub trait SliceLeft<T: Eq, U, S>: Strategy<(T, U)> + LeftSliced<T, U, SlicedLeft = S>
where
    Self: Sized,
{
    /// Get a strategy where all values are of the form `(left, x)`
    fn slice_left(self, left: T) -> S;
}

pub trait SliceRight<T, U: Eq, S>: Strategy<(T, U)> + RightSliced<T, U, SlicedRight = S>
where
    Self: Sized,
{
    /// Get a strategy where all values are of the form `(x, right)`
    fn slice_right(self, right: U) -> S;
}

pub trait IntersectBy<T: Eq, Other: Strategy<T> = Self> {
    #[must_use]
    /// Intersect the domains of two strategies, using `f` to compute the new weight elements
    fn intersect_by(
        self,
        other: &Other,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self;
}

pub trait Domain<T, S>: Strategy<T> {
    /// Get the set of elements that have a value in the strategy
    fn domain(self) -> S;
}

pub trait Singleton<T> {
    /// Return a new strategy where `x -> infinity`
    fn singleton(x: T) -> Self;
}

pub trait Length {
    /// Get the number of items in the domain of the strategy
    fn length(&self) -> usize;
}

pub trait Retain<T> {
    fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&StrategyItem<T>) -> bool;
}
