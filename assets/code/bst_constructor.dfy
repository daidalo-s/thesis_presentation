constructor (x: int)
    ensures fresh(Repr - {this})
    ensures Valid()
    ensures Contents == {x}
  {
    data := x;
    left := null;
    right := null;

    Repr := { this };
    Contents := { data };
  }