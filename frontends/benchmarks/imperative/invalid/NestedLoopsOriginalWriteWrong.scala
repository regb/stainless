import stainless.lang._

object NestedLoopsOriginalWriteWrong {
  case class Box(var v: BigInt)
  case class Holder(b: Box)

  // `h.b` is read for the first time inside the inner loop, and written through `b`:
  // every iteration of both loops must see the same box.
  def f(h: Holder): Unit = {
    require(h.b.v == 0)

    var i = BigInt(0)
    (while (i < 3) {
      decreases(3 - i)
      var j = BigInt(0)
      (while (j < 2) {
        decreases(2 - j)
        val b = h.b
        b.v = b.v + 1
        j += 1
      }).invariant(0 <= j && j <= 2 && h.b.v == 2 * i + j)
      i += 1
    }).invariant(0 <= i && i <= 3 && h.b.v == 2 * i)

    assert(h.b.v == 5)
  }
}
