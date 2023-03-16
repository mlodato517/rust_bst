pub(crate) enum DeleteResult<V> {
    /// The key wasn't found so nothing was deleted.
    NotFound,
    /// The Node returning this is being deleted and has no children. Its parent can take its `V`
    /// before dropping it.
    DeleteSelf,
    /// A child node was deleted yielding the value `V`.
    DeletedChild(V),
}
