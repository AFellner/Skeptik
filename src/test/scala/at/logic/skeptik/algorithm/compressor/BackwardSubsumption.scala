package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._

import scala.collection.mutable.{HashSet => MSet}

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

//@RunWith(classOf[JUnitRunner])
//class BackwardSubsumptionSpecification extends SpecificationWithJUnit {
object BackwardSubsumption {
  def main(args: Array[String]):Unit = {
	val testcase = 3
	
  val a = new Var("a",i)
  val b = new Var("b",i)
  val c = new Var("c",i)
  val d = new Var("d",i)
  val e = new Var("e",i)
	val f = new Var("f",i)
	val g = new Var("g",i)

	var concseq:SequentProofNode = null
	
	if (testcase == 0) {
    val sq1 = new Sequent(Seq(a,d),Seq())
    val sq2 = new Sequent(Seq(b,c),Seq(d))
    val sq3 = new Sequent(Seq(b,c),Seq(a))
    val sq4 = new Sequent(Seq(),Seq(a,c))
    val sq5 = new Sequent(Seq(),Seq(a,b,e))
    val sq6 = new Sequent(Seq(a,b),Seq())
    val sq7 = new Sequent(Seq(),Seq(b))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
    
    val r1 = R.apply(ax1, ax2)
    val r2 = R.apply(r1,ax3)
    val r3 = R.apply(r2,ax4)
    val r4 = R.apply(r3,ax5)
    val r5 = R.apply(ax6,ax7)
    concseq = R.apply(r4,r5)
	}
	else if (testcase == 1) {
    val sq1 = new Sequent(Seq(a,b,c),Seq())
    val sq2 = new Sequent(Seq(),Seq(c))
    val sq3 = new Sequent(Seq(),Seq(b))
    val sq4 = new Sequent(Seq(a,b),Seq())
    val sq5 = new Sequent(Seq(e),Seq(b))
    val sq6 = new Sequent(Seq(e),Seq(a))
    val sq7 = new Sequent(Seq(),Seq(a,e))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
    
    val r1 = R.apply(ax1, ax2) //ab
    val r2 = R.apply(r1,ax3) //a
    val r3 = R.apply(ax4,ax5) //ae
    val r4 = R.apply(r3,ax6) //e
    val r5 = R.apply(r4,ax7) //-a
    concseq = r5
	}
	else if (testcase == 2)
	{
	  val sq1 = new Sequent(Seq(a,b,c),Seq())
    val sq2 = new Sequent(Seq(),Seq(c))
    val sq3 = new Sequent(Seq(),Seq(a,b))
    val sq4 = new Sequent(Seq(a),Seq())
    val sq5 = new Sequent(Seq(),Seq(a,b))
    val sq6 = new Sequent(Seq(),Seq(a))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
  
    val r1 = R.apply(ax1, ax2) //ab
    val r2 = R.apply(ax3,ax4) //-b
    val r3 = R.apply(r1,r2) //a
    concseq = R.apply(r3,ax6)
	}
	else if (testcase == 3) {
	  val sq1 = new Sequent(Seq(b,c),Seq(a))
    val sq2 = new Sequent(Seq(),Seq(c))
	  val sq3 = new Sequent(Seq(),Seq(b))
    val sq4 = new Sequent(Seq(a,b),Seq())
    val sq5 = new Sequent(Seq(e),Seq(b))
    val sq6 = new Sequent(Seq(e),Seq(a))
    val sq7 = new Sequent(Seq(a),Seq(e))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
  
    val r1 = R.apply(ax1, ax2)
    val r2 = R.apply(r1,ax3)
    val r3 = R.apply(ax4,ax5)
    val r4 = R.apply(r3,ax6)
    val r5 = R.apply(r4,ax7)
    concseq = R.apply(r2,r5)
	}
	else if (testcase == 4) {
    val sq1 = new Sequent(Seq(a,b,c),Seq())
    val sq2 = new Sequent(Seq(),Seq(c))
    val sq3 = new Sequent(Seq(e),Seq(a))
    val sq4 = new Sequent(Seq(a,b),Seq())
    val sq5 = new Sequent(Seq(),Seq(b))
    val sq6 = new Sequent(Seq(),Seq(a,b))
    val sq7 = new Sequent(Seq(a,b,c,d),Seq())
    val sq8 = new Sequent(Seq(),Seq(c))
    val sq9 = new Sequent(Seq(),Seq(d,e))
    val sq10 = new Sequent(Seq(),Seq(a))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
    val ax8 = new Axiom(sq8)
    val ax9 = new Axiom(sq9)
    val ax10 = new Axiom(sq10)
  
    val r1 = R.apply(ax1, ax2) //ab
    val r2 = R.apply(r1,ax3) //be
    
    val r3 = R.apply(ax4,ax5) //a
    val r4 = R.apply(r3,ax6) //-b
    
    val r5 = R.apply(ax7,ax8) //abd
    val r6 = R(r5,ax9) //a,b,-e
    val r7 = R(r6,ax10) //b,-e
    
    val r8 = R(r2,r4) //e
    val r9 = R(r7,r4) //-e
//    println(r8.conclusion)
//    println(r9.conclusion)
    concseq = R.apply(r8,r9)
  }
	else if (testcase == 5) {
	  val n2 = new Axiom(new Sequent(Seq(),Seq(a,b)))
    val ax2 = new Axiom(new Sequent(Seq(),Seq(e)))
    val ax3 = new Axiom(new Sequent(Seq(b,e),Seq()))
    val ax4 = new Axiom(new Sequent(Seq(e,a),Seq()))
	  
	  val r1 = R(ax2,ax3) //b
	  val p = R(n2,r1) //-a
	  val n1 = R(ax2,ax4) //a
	  concseq = R(p,n1)
	}
	else if (testcase == 6) {
	  
	}
//	val sq = new Sequent(Seq(a,d),Seq())
//	val test1 = new Axiom(sq)
//	val test2 = new Axiom(sq)
//	val replaced = new MSet[SequentProofNode]
//	replaced += test1
//	println((test1.conclusion subsequentOf test2.conclusion) && (test2.conclusion subsequentOf test1.conclusion))
//	
  val proof = new Proof(concseq:SequentProofNode)
    def visit(node: SequentProofNode, results: Seq[Unit]):Unit = {
      println(node)
    }
    
    proof foldDown(visit)
    
//    proof bottomUp(visit)
//  println(proof)
   val compproof = BottomUpRightLeftSubsumptionTime(concseq)
 (compproof foldDown(visit))
  
//  "Backward Subsumption" should {
//    "compress the proof" in {
//      proof.size must beGreaterThan(compproof.size)
//    }
//    "conclude the empty clause" in {
//      compproof.root.conclusion.isEmpty must beTrue
//    }
	}
}