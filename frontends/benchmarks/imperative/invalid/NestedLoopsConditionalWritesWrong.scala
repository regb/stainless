import stainless.lang._

object NestedLoopsConditionalWritesWrong {
  final class Counter(var x: BigInt)

  // Each inner loop writes `c.x` under its own condition. At the head of the outer loop, these
  // conditions are about variables of the inner loop bodies that are out of scope.
  def count(c: Counter, a: Array[Int], rounds: Int): Unit = {
    require(0 <= rounds)
    val x0 = c.x
    var k = 0
    (while (k < rounds) {
      decreases(rounds - k)
      var i = 0
      (while (i < a.length) {
        decreases(a.length - i)
        if (a(i) != 2 && a(i) != 3) c.x = c.x + 1
        i += 1
      }).invariant(0 <= i && i <= a.length && x0 <= c.x)
      i = 0
      (while (i < a.length) {
        decreases(a.length - i)
        if (a(i) == 1) c.x = c.x + 1
        i += 1
      }).invariant(0 <= i && i <= a.length && x0 <= c.x)
      k += 1
    }).invariant(0 <= k && k <= rounds && x0 <= c.x)
  }.ensuring(_ => old(c).x == c.x)
}
