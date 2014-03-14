package at.logic.skeptik.pebbler

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.algorithm.compressor.pebbler._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}

object SpaceMeasureTest {
  def main(args: Array[String]):Unit = {
    val testcase = 0
    val a = new Var("a",i)
    val b = new Var("b",i)
    val c = new Var("c",i)
    val d = new Var("d",i)
    val e = new Var("e",i)
    val f = new Var("f",i)
    val g = new Var("g",i)
    var concseq:SequentProofNode = null
//    if (testcase == 0) {
      val n1 = new Axiom(new Sequent(Seq(),Seq(a,b)))
      val n2 = new Axiom(new Sequent(Seq(b),Seq()))
      val n3 = R(n1,n2)
      val n4 = new Axiom(new Sequent(Seq(a),Seq(b)))
      val n5 = R(n2,n4)
      concseq = R(n3,n5)
//    }
    val proof = new Proof(concseq)
    println(proof)
    measure(proof)("space")
    println("------")
    val proof2 = new Proof(concseq, IndexedSeq(n1,n2,n4,n5,n3,concseq).reverse)
    measure(proof2)("space")
  }
}