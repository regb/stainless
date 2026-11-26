import stainless.lang._

object NestedReadVarIndex {
  def f(a: Array[Array[BigInt]], r: Int): BigInt = {
    require(0 <= r && r < a.length)

    // A var on purpose: only a var row index gets bound around each `a(i)` read
    var i = r
    var s = BigInt(0)
    var j = 0
    (while (j < a(i).length) {
      decreases(a(i).length - j)
      s = s + a(i)(j)
      j += 1
    }).invariant(0 <= i && i < a.length && 0 <= j && j <= a(i).length)
    s
  }
}
