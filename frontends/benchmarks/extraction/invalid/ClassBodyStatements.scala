import stainless.lang.*

/** Statements in the bodies of classes and traits, which are not extracted and must be rejected. */
object ClassBodyStatements:

  case class A(x: BigInt):
    require(x >= 0) // allowed: a class invariant
    assert(x > 0) // not allowed here
    def get: BigInt = x

  class B(x: BigInt):
    assert(false) // not allowed here
    val y: BigInt = x
    x + 1 // not allowed here

  trait C:
    assert(false) // not allowed here

  def anon(): C = new C:
    assert(false) // not allowed here
