method RemoveMin() returns (min: int, node: TreeNode?)
  requires Valid()
  modifies Repr
  ensures fresh(Repr - old(Repr))
  ensures node != null ==> node.Valid()
  ensures node == null ==> old(Contents) == {min}
  ensures node != null ==> node.Repr <= Repr && node.Contents == old(Contents) - {min}
  ensures min in old(Contents) && (forall x :: x in old(Contents) ==> min <= x)
  decreases Repr
{
  if left == null {
    min := data;
    node := right;
  } else {
    var t;
    min, t := left.RemoveMin();
    left := t;
    node := this;
    Contents := Contents - {min};
    if left != null { Repr := Repr + left.Repr; }
  }
}