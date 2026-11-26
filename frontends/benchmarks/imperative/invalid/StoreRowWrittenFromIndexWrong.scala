import stainless.lang._

object StoreRowWrittenFromIndexWrong {
  // A new row is written with a value read from `col`, then stored at `m(col)`: the row is reachable
  // from `m` only, and copying the value of `col` into it creates no alias.
  def build(m: Array[Array[Int]]): Unit = {
    var col = 0
    (while (col < m.length) {
      decreases(m.length - col)
      val column = Array.fill(1)(0)
      column(0) = col
      m(col) = column
      col += 1
    }).invariant(0 <= col && col <= m.length)
    assert(col == 0)
  }
}
