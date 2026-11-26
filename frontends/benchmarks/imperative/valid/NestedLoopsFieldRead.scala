import stainless.lang._
import stainless.collection._

object NestedLoopsFieldRead {
  case class Grid(w: Int, walls: Array[Boolean])
  case class State(dist: Array[Int], queue: Array[Int])

  // A breadth-first search on a grid, run once per source: the fields of `g` and `st`
  // are first read in the innermost of three nested loops.
  inline def bfs(g: Grid, src: Int, st: State): Unit = {
    require(0 < g.w && g.w <= 1000 && st.dist.length <= 1000000 && g.walls.length == st.dist.length && st.queue.length == st.dist.length && 0 <= src && src < st.dist.length)

    st.dist(src) = 0
    st.queue(0) = src
    var head = 0
    var tail = 1
    (while (head < tail) {
      decreases(st.dist.length - head)
      val u = st.queue(head)
      head += 1
      var dir = 0
      (while (dir < 4 && 0 <= u && u < st.dist.length) {
        decreases(4 - dir)
        val v = if (dir == 0) u + 1 else if (dir == 1) u - 1 else if (dir == 2) u + g.w else u - g.w
        if (0 <= v && v < st.dist.length && !g.walls(v) && st.dist(v) == -1 && tail < st.queue.length) {
          st.dist(v) = 1
          st.queue(tail) = v
          tail += 1
        }
        dir += 1
      }).invariant(0 <= dir && dir <= 4 && 0 < head && head <= tail && tail <= st.queue.length &&
        0 < g.w && g.w <= 1000 && st.dist.length <= 1000000 && g.walls.length == st.dist.length && st.queue.length == st.dist.length)
    }).invariant(0 <= head && head <= tail && tail <= st.queue.length &&
      0 < g.w && g.w <= 1000 && st.dist.length <= 1000000 && g.walls.length == st.dist.length && st.queue.length == st.dist.length)
  }

  def fillShortestPathsFrom(g: Grid, sources: List[Int], st: State): Unit = {
    require(0 < g.w && g.w <= 1000 && st.dist.length <= 1000000 && g.walls.length == st.dist.length && st.queue.length == st.dist.length)

    var l = sources
    (while (l.nonEmpty) {
      decreases(l)
      val s = l.head
      if (0 <= s && s < st.dist.length) {
        bfs(g, s, st)
      }
      l = l.tail
    }).invariant(0 < g.w && g.w <= 1000 && st.dist.length <= 1000000 && g.walls.length == st.dist.length && st.queue.length == st.dist.length)
  }
}
