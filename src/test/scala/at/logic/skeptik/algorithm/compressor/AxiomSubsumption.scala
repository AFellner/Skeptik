package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

@RunWith(classOf[JUnitRunner])
class AxiomSubsumptionSpecification extends SpecificationWithJUnit {
  val testcase = 0
  
  val a = new Var("a",i)
  val b = new Var("b",i)
  
  var concseq:SequentProofNode = null
  
  if (testcase == 0) {
 
    val sq1 = new Sequent(Seq(b),Seq(a))
    val sq2 = new Sequent(Seq(a),Seq(b))
    val sq3 = new Sequent(Seq(),Seq(a))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    
    val r1 = R.apply(ax2, ax3)
    concseq = R(r1,ax1)
  }
  else {
    val sq1 = new Sequent(Seq(a),Seq())
    val sq2 = new Sequent(Seq(b),Seq(a))
    val sq3 = new Sequent(Seq(a),Seq(b))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    
    val r1 = R.apply(ax1, ax2)
    concseq = R(r1,ax3)
  }
  val proof = Proof(concseq:SequentProofNode)
  println(proof)
  val compproof = LeftRightAxiomSubsumption(concseq)
  println(compproof)
  
  val compproof2 = RightLeftAxiomSubsumption(concseq)
  println(compproof2)
    
  "Backward Subsumption" should {
    "compress the proof" in {
      proof.size must beGreaterThan(compproof.size)
    }
    "conclude the empty clause" in {
      compproof.root.conclusion.isEmpty must beTrue
    }
  }
}