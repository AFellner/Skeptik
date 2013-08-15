package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._

import scala.collection.mutable.{HashSet => MSet}
import scala.collection.mutable.{HashMap => MMap}

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

//@RunWith(classOf[JUnitRunner])
//class BackwardSubsumptionSpecification extends SpecificationWithJUnit {
object BackwardSubsumption1 {
  def main(args: Array[String]):Unit = {
  val testcase = 2
  
  val a = new Var("a",i)
  val b = new Var("b",i)
  val c = new Var("c",i)
  val d = new Var("d",i)
  val e = new Var("e",i)
  val f = new Var("f",i)
  val g = new Var("g",i)

  var concseq:SequentProofNode = null
  var firstNode:SequentProofNode = null
  
  if (testcase == 0) {
    val n1 = new Axiom(new Sequent(Seq(a),Seq()))
    val n2 = new Axiom(new Sequent(Seq(),Seq(a,b)))
    val n3 = R(n1,n2)
    val n4 = new Axiom(new Sequent(Seq(b),Seq(a)))
    val n5 = R(n3,n4)
    val n6 = new Axiom(new Sequent(Seq(),Seq(a)))
    val n7 = new Axiom(new Sequent(Seq(a),Seq(c)))
    val n8 = R(n6,n7)
    //println(n8)
    val n9 = new Axiom(new Sequent(Seq(a,c),Seq()))
    val n10 = R(n8,n9)
    concseq = R.apply(n5,n10)
    
    firstNode = n7
  }
  else if (testcase == 1) {
    val n1 = new Axiom(new Sequent(Seq(),Seq(c,b)))
//    val n2 = new Axiom(new Sequent(Seq(c),Seq(a)))
    
    val n4 = new Axiom(new Sequent(Seq(b),Seq(c)))
    val n5 = new Axiom(new Sequent(Seq(),Seq(a,b)))
    val n6 = new Axiom(new Sequent(Seq(a,d),Seq()))
    val n7 = R(n5,n6)
    val n8 = new Axiom(new Sequent(Seq(b,c),Seq()))
    val n9 = R(n7,n8)
    val n10 = R(n4,n9)
    
    val n12 = new Axiom(new Sequent(Seq(a),Seq(c)))
    val n13 = new Axiom(new Sequent(Seq(a),Seq(e)))
    val n14 = new Axiom(new Sequent(Seq(),Seq(a,d)))
    val n15 = new Axiom(new Sequent(Seq(c,d),Seq()))

    val n16 = R(n14,n15)
    val n3 = R(n1,n16)
    val n11 = R(n3,n10)
    val n17 = R(n13,n16)
    val n18 = R(n12,n17)
    concseq = R.apply(n11,n18)
    
    firstNode = n7
  }
  else if (testcase == 2) {
    val n1 = new Axiom(new Sequent(Seq(),Seq(a,b)))
    val n2 = new Axiom(new Sequent(Seq(),Seq(c,b)))
    val n3 = new Axiom(new Sequent(Seq(),Seq(a,d)))
    val n4 = new Axiom(new Sequent(Seq(c,d),Seq()))
    val n5 = R(n3,n4) // c |- a
    val n6 = R(n2,n5) // |- ab
    val n7 = new Axiom(new Sequent(Seq(b),Seq(c)))
    val n8 = new Axiom(new Sequent(Seq(a,d),Seq()))
    val n9 = R(n1,n8) // d |- b
    val n10 = new Axiom(new Sequent(Seq(b,c),Seq()))
    val n11 = R(n10,n9) // dc |-
    val n12 = R(n7,n11) // bd |-
    val n13 = R(n12,n6) // d |- a
    val n14 = new Axiom(new Sequent(Seq(a,b),Seq()))
    val n15 = R(n13,n14)
    concseq = R(n1,n15)
    
    firstNode = n7
  }
  else {
    val n1 = new Axiom(new Sequent(Seq(),Seq(c,b)))
//    val n2 = new Axiom(new Sequent(Seq(c),Seq(a)))
    
    val n4 = new Axiom(new Sequent(Seq(b),Seq(c)))
    val n5 = new Axiom(new Sequent(Seq(),Seq(a,b)))
    val n6 = new Axiom(new Sequent(Seq(a,d),Seq()))
    val n7 = R(n5,n6)
    val n8 = new Axiom(new Sequent(Seq(b,c),Seq()))
    val n9 = R(n7,n8)
    val n10 = R(n4,n9)
    
    val n12 = new Axiom(new Sequent(Seq(a),Seq(c)))
    val n13 = new Axiom(new Sequent(Seq(a),Seq(e)))
    val n14 = new Axiom(new Sequent(Seq(),Seq(a,d)))
    val n15 = new Axiom(new Sequent(Seq(c,d),Seq()))

    val n16 = R(n14,n15)
    val n3 = R(n1,n16)
    val n11 = R(n3,n10)
    val n17 = R(n13,n16)
    val n18 = R(n12,n17)
    val extra1 = new Axiom(new Sequent(Seq(a),Seq(d)))
    val extra2 = R(n5,extra1)
    val n19 = R(n11,n18)
    concseq = R(extra2,n19)
    
    firstNode = n7
  }
  
  val nodeCount = MMap[SequentProofNode,Int]()
  val nodes = MSet[SequentProofNode]()
  var count = 1
  var storeNodes = true
  var x:Option[SequentProofNode] = Option.empty
  val y = new Next[SequentProofNode]
  
  val proof = new Proof(concseq:SequentProofNode)
    def visit(node: SequentProofNode, results: Seq[SequentProofNode]):SequentProofNode = {
      println(count + ": "+ node)
      nodeCount += (node -> count)
      if (storeNodes) nodes += node
      count = count +1
      if (count == 2) {
//        y.n = Some(concseq)
      }
      else {
        y.n = None
      }
      node
    }
  
  def printProof(proof: Proof[SequentProofNode]) = {
    
    var counter = 0; var result = "";
    proof foldDown { (n:SequentProofNode, r:Seq[Int]) =>
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t: " +
                n.name + "(" + r.mkString(", ") + ")[" + n.parameters.mkString(", ") + "]" + " ~ " + n.hashCode()
      if (!(nodes contains n)) result += " not original"
      result += "\n"
      counter
    }
    result
  }
 
  def ancOfItself(node: SequentProofNode, results: Seq[Unit]):Unit = {
      println(BottomUpRightLeftSubsumptionTime.notAncestor(node, node))
    }
  def notOriginal(node: SequentProofNode, results: Seq[Unit]):Unit = {
    if (!(nodes contains node)) {
      println(node + " is not original")
    }
  }
//    println(proof)
//    println(concseq)
//  proof.foldDown3(visit)(y)
//    proof foldDown (visit)
//    print(printProof(proof))
//    println()
//    proof bottomUp(visit)
  println(proof)
   val compproof = BottomUpLeftRightSubsumptionMemory(concseq)
//   print(printProof(compproof))
   println(compproof)
 
//   compproof foldDown notOriginal
  
//  "Backward Subsumption" should {
//    "compress the proof" in {
//      proof.size must beGreaterThan(compproof.size)
//    }
//    "conclude the empty clause" in {
//      compproof.root.conclusion.isEmpty must beTrue
//    }
  }
}