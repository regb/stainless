import stainless.lang._

object NestedWriteVarIndexWrong {
  def f(a: Array[Array[BigInt]]): Unit = {
    require(a.length > 1 && a(0).length > 0 && a(1).length > 0)

    var i = 0
    a(i)(0) = 7
    i = 1
    assert(a(i)(0) == 7)
  }
}
