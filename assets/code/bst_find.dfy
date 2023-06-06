method Find(x: int) returns (present: bool)
  requires Valid()
  ensures present <==> x in Contents
  decreases Repr
  ensures Valid()
{
  if x == data
  {
    present := true;
  }
  else if left != null && x < data
  {
    present := left.Find(x);
  }
  else if right != null && data < x
  {
    present := right.Find(x);
  }
  else
  {
    return false;
  }
}