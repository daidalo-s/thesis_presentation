method Insert(x: int)
  requires Valid()
  modifies Repr
  ensures Valid() && fresh(Repr - old(Repr)) && Contents == old(Contents) + {x}
  decreases Repr
{
  if x == data { return; }
  if x < data {
    if left == null {
      left := new TreeNode(x);
    } else {
      left.Insert(x);
    }
    Repr := Repr + left.Repr;
  } else {
    if right == null {
      right := new TreeNode(x);
    } else {
      right.Insert(x);
    }
    Repr := Repr + right.Repr;
  }
  Contents := Contents + {x};
}