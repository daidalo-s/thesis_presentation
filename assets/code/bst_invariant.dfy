ghost predicate Valid()
  reads this, Repr
{
  this in Repr &&
  (left != null ==>
     left in Repr &&
     left.Repr <= Repr && this !in left.Repr &&
     (forall e :: e in left.Contents ==> e < data) && // BST
     left.Valid()) &&
  (right != null ==>
     right in Repr &&
     right.Repr <= Repr && this !in right.Repr &&
     (forall e :: e in right.Contents ==> data < e) && // BST
     right.Valid())
  && (left != null && right != null ==> left.Repr !! right.Repr)
  && Contents == (if left == null then {} else left.Contents) +
                 (if right == null then {} else right.Contents) +
                 {data}
}