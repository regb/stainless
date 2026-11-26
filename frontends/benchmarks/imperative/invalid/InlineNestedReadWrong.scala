import stainless.lang._

object InlineNestedReadWrong {
  inline def cell(a: Array[Array[BigInt]], i: Int, j: Int): BigInt = {
    require(0 <= i && i < a.length && 0 <= j && j < a(i).length)
    a(i)(j)
  }

  def f(a: Array[Array[BigInt]]): BigInt = {
    var s = BigInt(0)
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      s = s + cell(a, i, 0)
      i += 1
    }).invariant(0 <= i && i <= a.length)
    s
  }
}
