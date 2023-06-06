method Remove(x: int) returns (node: TreeNode?)
  requires Valid()
  modifies Repr
  ensures fresh(Repr - old(Repr))
  ensures node != null ==> node.Valid()
  ensures node == null ==> old(Contents) <= {x}
  ensures node != null ==> node.Repr <= Repr && node.Contents == old(Contents) - {x}
  decreases Repr
{
  node := this;
  if left != null && x < data {
    var t := left.Remove(x);
    left := t;
    Contents := Contents - {x};
    if left != null { Repr := Repr + left.Repr; }
  } else if right != null && data < x {
    var t := right.Remove(x);
    right := t;
    Contents := Contents - {x};
    if right != null { Repr := Repr + right.Repr; }
  } else if x == data {
    if left == null && right == null {
      node := null;
    } else if left == null {
      node := right;
    } else if right == null {
      node := left;
    } else {
      // rotate
      var min, r := right.RemoveMin();
      data := min;  right := r;
      Contents := Contents - {x};
      if right != null { Repr := Repr + right.Repr; }
    }
  }
}