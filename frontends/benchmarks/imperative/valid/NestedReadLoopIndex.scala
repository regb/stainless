import stainless.lang._

object NestedReadLoopIndex {
  def f(a: Array[Array[BigInt]]): BigInt = {
    var s = BigInt(0)
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i).length > 0) s = s + a(i)(0)
      i += 1
    }).invariant(0 <= i && i <= a.length)
    s
  }
}
